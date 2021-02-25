(ns ribelo.pathos
  (:refer-clojure :exclude [resolve])
  (:require
   [clojure.core.async :as a]
   [meander.epsilon :as m]
   [taoensso.encore :as e]
   [taoensso.timbre :as timbre]
   [clojure.set :as set]))

(declare graph-traversal resolve)

(m/defsyntax dbg [pattern]
  `(m/app #(doto % prn) ~pattern))

(def cache_
  "information about nodes and edges of the graph is written to one global atom"
  (atom {}))

(defn -reset-cache!
  "resets the atom and clears all data"
  []
  (reset! cache_ {}))

(defn add-ns-to-map [ns m]
  (persistent!
   (reduce-kv
    (fn [acc k v]
      (assoc! acc (e/merge-keywords [ns k]) v))
    (transient {})
    m)))

(defn change-ns-in-map [ns m]
  (persistent!
   (reduce-kv
    (fn [acc k v]
      (assoc! acc (e/merge-keywords [ns (name k)]) v))
    (transient {})
    m)))

(m/defsyntax ns-keys? [ns-pattern name-pattern]
  `(m/and
    (m/pred qualified-keyword?)
    (m/app namespace ~ns-pattern)
    (m/app name ~name-pattern)))

(defn- optional-input?
  "checks if the argument symbol or keyword starts of \"?\""
  [k]
  (m/rewrite k
    (m/pred ident? (m/app (juxt namespace name) [?ns ?name]))
    (m/cata ?name)
    ;;
    (m/pred string? (m/re #"^\?.+"))
    true))

(defn- required-input?
  "checks if the symbol or key name doesn't starts with ?"
  [k]
  (m/rewrite k
    (m/pred ident? (m/app (juxt namespace name) [?ns ?name]))
    (m/cata ?name)
    ;;
    (m/pred string? (m/not (m/re #"^\?.+")))
    true))

(defn parse-input
  "parses the vector of function arguments to find all edges that enter the node"
  [body]
  (m/rewrite body
    ;; {:input [!ks ...]}
    ((m/pred vector?) {::input [(m/pred keyword? !ks) ...]} & _)
    [!ks ...]
    ;; {:keys [a/b b/c]}
    ([{:keys (m/some (m/gather (m/pred required-input? !ks)))}] & _)
    ~(mapv keyword !ks)
    ;; {:a/keys [b c]}
    ([{(ns-keys? ?ns ?name) (m/gather (m/pred required-input? !ks))}] & _)
    [(m/app e/merge-keywords [?ns !ks]) ...]
    ;; {:a ?a :b ?b}
    ([(m/map-of _ (m/pred ident? !vs))] & _)
    ~(into [] (remove optional-input?) !vs)
    ([] & _) []))

(comment
  (parse-input '([a b c] {::input [:a :b :c]} (println "foo")))
  ;; => [:a :b :c]
  (parse-input '([{:keys [a/b a/c]}] (println "foo")))
  ;; => [:a/b :a/c]
  (parse-input '([{:keys [a/b a/c]}] {::memo true} (println "foo")))
  ;; => [:a/b :a/c]
  (parse-input '([{:keys [a/b a/?c]}] (println "foo")))
  ;; => [:a/b]
  (parse-input '([{:a/keys [b c]}] {::memo true} (println "foo")))
  ;; => [:a/b :a/c]
  (parse-input '([{:a/keys [b ?c]}]))
  ;; => [:a/b]
  (parse-input '([{:keys [a ?b]}] (println "foo")))
  ;; => [:a]
  (parse-input '([{a :a/a b :a/b c :a/?c}] (println "foo")))
  ;; => [:a/a :a/b]
  (parse-input '([]))
  ;; => []
  )

(defn fn-inputs
  "parses the vector of function arguments to determine all the data needed for
  the resolver"
  [body]
  (m/rewrite body
    ;; {:keys [a/b b/c]}
    ([{:keys [!ks ...]} :as ?x] & _)
    ?x
    ;; {:a/keys [b c]}
    ([{(ns-keys? ?ns ?name) [!ks ...]}] & _)
    [{& [[~(e/merge-keywords [?ns ?name]) [!ks ...]] ...]}]
    ;; (mapv #(e/merge-keywords [?ns %]) !ks)
    ;; {:a ?a :b ?b}
    ([(m/map-of !ks !vs)] & _)
    [{& [[!ks !vs] ...]}]
    ([] & _) ['_m]))

(comment
  (fn-inputs '([{:keys [a ?b]}] (println "foo")))
  ;; => [{:keys [a ?b]}]
  (fn-inputs '([{:a/keys [b c]}] (println "foo")))
  (fn-inputs '([{:a/keys [b ?c]}] (println "foo")))
  ;; => [#:a{:keys [b ?c]}]
  (fn-inputs '([{:keys [a/b a/c]}] (println "foo")))
  ;; => [{:keys [a/b a/c]}]
  (fn-inputs '([{a :a/a b :a/b c :a/?c}] (println "foo")))
  ;; => [{a :a/a, b :a/b, c :a/?c}]
  (fn-inputs '([] (println "foo")))
  ;; => [_m]
  )

(defn parse-output
  "parses the function body to find all edges that escape the node"
  [body]
  (m/rewrite body
    (m/pred keyword? ?k)
    ?k
    ;;
    {(m/pred keyword? ?k) [(m/pred keyword? !ks) ...]}
    ?k
    ;;
    ((m/pred vector?) {::output [!xs ...]} & ?body)
    #{^& [(m/cata !xs) ...]}
    ;; {}
    (m/map-of (m/pred keyword? !ks) _)
    #{^& [(m/cata !ks) ...]}
    ;; (... {})
    (_ ... (m/cata (m/pred set? ?m)))
    ?m
    (_ ... (m/cata (m/pred keyword? ?m)))
    #{?m}))

(comment
  (parse-output '([x y] {::output [:a]} {:a 1 :b 2}))
  ;; => #{:a}
  (parse-output '([x y] {:a 1}))
  ;; => #{:a}
  (parse-output '([x y]
                  {::output [:e :f {:a [:b :c :d]}]}
                  (println "foo")))
  ;; => #{:e :f :a}
  (parse-output '([x y]
                  (let [a 1]
                    {:a 1})))
  ;; => #{:a}
  (parse-output '([x y]
                  (let [a 1]
                    (-> m :k))))
  ;; => #{:k}
  (parse-output '([x y]
                  (-> [{:woeid 1111} {:woeid 2222}]
                      first
                      :woeid)))
  ;; => #{:woeid}
  )

(defn parse-body
  "parses the function body to check memoization and to find required arguments"
  [body]
  (m/rewrite body
    ;;
    ((m/pred vector?) {:as ?body})
    {:memo? false
     :args  []
     :body  (?body)}
    ;; memoize
    ((m/pred vector?) {::memoize true} & ?body)
    {:memo? true
     :args  []
     :body  ?body}
    ;; custom memoize
    ((m/pred vector?) {::memoize [!args ...]} & ?body)
    {:memo? true
     :args  [!args ...]
     :body  ?body}
    ;; no memoize
    ((m/pred vector?) {} & ?body)
    {:memo? false
     :args  []
     :body  ?body}
    ;; no opts
    ((m/pred vector?) & ?body)
    {:memo? false
     :args  []
     :body  ?body}))

(comment
  (parse-body '([x y] {:a/b 1.0}))
  ;; => {:memo? false, :args [], :body (#:a{:b 1.0})}
  (parse-body '([x y] (println "foo")))
  ;; => {:memo? false, :args [], :body ((println "foo"))}
  (parse-body '([x y] {::memoize true} (println "foo")))
  ;; => {:memo? true, :args [], :body ((println "foo"))}
  (parse-body '([x y] {::memoize [(e/ms :mins 5)]} (println "foo")))
  ;; => {:memo? true, :args [(e/ms :mins 5)], :body ((println "foo"))}
  (parse-body '([x y] {::inputs [:a/b]} (println "foo")))
  ;; => {:memo? false, :args [], :body ((println "foo"))}
  )

(defn entity->resolvers
  "finds the resolvers that produces the given entity"
  [entity]
  (m/search @cache_
    {?id {:out {~entity _}}}
    ?id))

(defn entity->resolver
  "finds the fastest resolver that produces the given entity"
  [entity]
  (->> (m/search @cache_
         {?id {:out {~entity _}
               :ms  ?ms}}
         [?id ?ms])
       (sort-by second)
       (ffirst)))

(defn entities->resolvers
  "finds fastest resolvers needed to produces given entities"
  [ids]
  (into [] (comp (map entity->resolver) (remove nil?) (distinct)) ids))

(defn ->cost
  "find out the cost of the resolver"
  ([id]
   (m/find @cache_
     {~id {:ms ?ms}}
     ?ms
     ::empty 0))
  ([id resolved]
   (if-not ((set resolved) id)
     (->cost id)
     0.0)))

(defn memoized-resolver?
  "checks if the given resolver is memoized"
  [id]
  (m/find @cache_
    {~id {:memo? ?memo}} ?memo))

;; much faster than meander
(defn resolver->fn
  "takes the function assigned to the resolver"
  [id]
  (get-in @cache_ [id :f]))

(defn resolver-exists?
  "checks if a resolver with the given id exists"
  [id]
  (m/find @cache_
    {~id {:type :resolver}} true))

;; much faster than meander
(defn resolver->entities
  "specifies the data needed by the resolver"
  [id]
  (get-in @cache_ [id :in]))

(comment
  (-> (entity->resolvers :person/last-name)
      (resolver->entities)))

(defn- resolver-fn
  "returns a parsed function with or without memoization and with parsed function
  arguments"
  [body]
  (e/when-let [input                     (fn-inputs body)
               {:keys [memo? args body]} (parse-body body)]
    (if memo?
      `(e/memoize ~@args (fn ~input ~@body))
      `(fn ~input ~@body))))

(defn -reg-resolver
  "writes the resolver to cache."
  [{:keys [id in out f memo?]}]
  (and
   (e/have fn? f)
   (e/have not-empty out)
   (e/have map? out))
  (when (resolver-exists? id)
    (timbre/warn "pathos overwriting resolver:" id))
  (graph-traversal :mem/del :mem/all)
  (resolve :mem/del :mem/all)
  (swap! cache_ assoc id {::id    id
                          :type   :resolver
                          :f      f
                          :in     in
                          :out    out
                          :ms     0.0
                          :ncalls 0
                          :memo?  memo?})
  (doseq [[k _] out]
    (swap! cache_ update k (fn [m] (-> (assoc m ::id k :type :node)
                                       (update :f (fnil conj #{}) id)))))
  id)

(defmacro reg-resolver
  "creates a resolver with the given id. automatically determines the arguments
  needed and what function produces the output."
  {:style/indent :defn}
  [id & body]
  (e/have qualified-keyword? id)
  (let [{:keys [memo?]} (parse-body body)]
    `(-reg-resolver
      {:id    ~id
       :in    ~(set (parse-input body))
       :out   ~(parse-output body)
       :f     ~(resolver-fn body)
       :memo? ~memo?})))

(defmacro reg-resolver-eq
  "helper function that creates an equivalent resolver for the given output id"
  [x y]
  (let [id (e/merge-keywords [(str *ns*) x "eq" y])]
    `(reg-resolver ~id [{~'v ~y}] {~x ~'v})))

(defn update-time!
  "updates the execution cost of the resolver"
  [id ms*]
  (e/swap-in! cache_ [id]
    (fn [{:keys [^long ncalls ^double ms] :as m}]
      (let [avg (/ (+ (*  ncalls ms) ms*) (inc ncalls))]
        (-> m
            (assoc :ms avg)
            (update :ncalls inc))))))

(defmacro with-time-ms
  "macro establishes the execution time of the body and returns a vector, where
  the first variable is milliseconds and the second is the body result"
  [& body]
  `(let [t0# (e/now-udt*)
         r#  ~@body
         t1# (e/now-udt*)]
     [(- t1# t0#) r#]))

(defn execute
  "execute the function assigned to the resolver with the given id"
  ([id] (execute id {}))
  ([id m]
   (let [f      (resolver->fn id)
         [ms r] (with-time-ms (f m))]
     (update-time! id ms)
     r)))

(defn satisfies-inputs?
  "checks if the map has all the necessary keys needed for the resolver with the
  given id"
  [id xs]
  (m/match xs
    (m/pred map? ?m)
    (set/superset? (set (keys ?m)) (resolver->entities id))
    ;;
    (m/pred set? ?set)
    (set/superset? ?set (resolver->entities id))))

(comment
  (satisfies-inputs? ::person {:db/id :ivan}))

(defn process-chain
  "calls the individual resolvers that make up the chain"
  ([chain] (process-chain chain {}))
  ([chain args]
   (reduce
    (fn [acc id]
      (merge (execute id acc) acc))
    args
    chain)))

(defn process-chain-async
  "async calls the individual resolvers that make up the chain"
  ([chain] (process-chain-async chain {}))
  ([chain args]
   (let [m_ (atom args)]
     (loop [chain* chain chans* []]
       (e/cond
         (seq chain*)
         (let [xs    (filter #(satisfies-inputs? % @m_) chain*)
               rst   (into [] (remove (set xs)) chain*)
               chans (mapv (fn [id]
                             (a/go
                               (let [m* (execute id @m_)]
                                 (swap! m_ merge m*))))
                           xs)]
           (recur rst (into chans* chans)))
         (seq chans*)
         (let [[_v p] (a/alts!! chans*)]
           (recur chain* (into [] (remove #{p}) chans*)))
         :else @m_)))))

(defn process-output
  "poor man's eql"
  [output selectors]
  (m/rewrite [output selectors]
    ;; init
    [{:as ?m} [(m/or (m/pred keyword? !xs) (m/pred map? !xs)) ...]]
    {& [(m/cata [?m !xs]) ...]}
    ;; ?m ?keyword
    [{?k ?v :as ?m} (m/pred keyword? ?k)]
    {?k ?v}
    ;; no ?k in ?m
    [{:as ?m} (m/pred keyword? ?k)]
    {}
    ;; ?m {?k [?xs]}}
    [{?k (m/pred vector? ?v) :as ?m} {(m/pred keyword? ?k) [(m/pred keyword? !ks) ...]}]
    {?k [& (m/cata [?v !ks])]}
    ;; ?m {?k [?xs]}
    [{?k {:as ?v} :as ?m} {(m/pred keyword? ?k) [(m/pred keyword? !ks) ...]}]
    {?k (m/cata [?v !ks])}
    ;; ?m {?k {?k ...}}
    [{?k ?v :as ?m} {(m/pred keyword? ?k) {(m/pred keyword? ?x) ?y :as ?z}}]
    {?k {& (m/cata [?v [?z]])}}
    ;; vvv
    [[{:as !maps} ...] (m/pred keyword? ?k)]
    (m/cata [(m/cata [!maps ?k]) ...])
    ;; vvv
    (m/gather (m/pred not-empty !maps))
    [!maps ...]))

(comment
  (let [data {:a 1
              :b 2
              :c [{:d 1} {:d 2} {:e 3}]
              :f {:g 1}
              :h {:i [{:j 1} {:j 2}]}
              :k {:l {:m 1}}}]
    (process-output
     data
     [:a
      :b
      {:c [:d]}
      {:f [:g]}
      {:h {:i [:j]}}
      {:k {:l [:m]}}]))
  ;; =>
  ;; {:a 1,
  ;;  :b 2,
  ;;  :c [{:d 1} {:d 2}]
  ;;  , :f
  ;;  {:g 1} ,
  ;;  :h {:i [{:j 1} {:j 2}]}
  ;;  , :k
  ;;  {:l {:m 1}}}
  )

(def graph-traversal
  (e/memoize
    (e/ms :mins 15)
    (fn
      ([entity] (graph-traversal entity #{}))
      ([entity provided]
       (let [resolver (entity->resolver entity)]
         (loop [id resolver rst [] chain [] req #{} provides provided]
           (if id
             (let [outputs            (resolver->entities id)
                   inputs             (into []  (remove provided) (resolver->entities id))
                   req*               (into req (resolver->entities id))
                   [nxt & resolvers*] (into rst (entities->resolvers inputs))]
               (recur nxt
                      (vec resolvers*)
                      (conj chain id)
                      req*
                      (into provides outputs)))
             {:chain    (into [] (distinct) chain)
              :provides provides
              :req      req})))))))

(def resolve
  (e/memoize
    (e/ms :mins 15)
    (fn ([entities]
        (resolve entities #{}))
      ([entities provided]
       (resolve entities provided #{}))
      ([entities provided resolved]
       (loop [[entity & entities*] (into [] (remove provided) entities)
              req*                 #{}
              provides*            provided
              resolved*            resolved
              chain*               []]
         (if entity
           (let [resolver (entity->resolvers entity)]
             (let [{:keys [chain req provides]} (graph-traversal entity provides*)
                   req*                         (into req* req)
                   provides*                    (into provides* provides)
                   entities*                    (into [] (remove provides*) entities*)]
               (recur entities*
                      req*
                      provides*
                      (conj resolved* resolver)
                      (into chain* chain))))
           (if (set/superset? provides* req*)
             (reverse chain*)
             (do
               (timbre/warnf "lack of required entities %s"
                             (set/difference req* provides*))
               (reverse (filter #(satisfies-inputs? % provides*) chain*))))))))))

(defn selector->keys [selector]
  (m/rewrite selector
    [!sel ...]
    [(m/cata !sel) ...]
    ;;
    (m/pred keyword? ?k)
    ?k
    ;;
    {(m/pred keyword? ?k) _}
    ?k))

(defn eql
  ([selector] (eql {} selector))
  ([args selector]
   (some-> (resolve (selector->keys selector) (set (keys args)))
           (process-chain-async args)
           (process-output selector))))

(comment

  (-reset-cache!)
  ;;          a
  ;;         / \
  ;;        b   c
  ;;       /     \
  ;;      d - f - e
  ;;        /   \
  ;;       g     k
  ;;      /       \
  ;;   i-h         l-n
  ;;     |         |
  ;;     j         m
  (do (reg-resolver ::a
        [{:keys [b c]}]
        {:a (+ b c)})
      (reg-resolver ::b
        [{:keys [e]}]
        {:b (inc e)})
      (reg-resolver ::c
        [{:keys [d]}]
        {:c (inc d)})
      (reg-resolver ::e
        [{:keys [f]}]
        {:e (inc f)})
      (reg-resolver ::d
        [{:keys [f]}]
        {:d (inc f)})
      (reg-resolver ::f
        [{:keys [g k]}]
        {:f (+ g k)})
      (reg-resolver ::g
        [{:keys [h]}]
        {:g (inc h)})
      (reg-resolver ::h
        [{:keys [i j]}]
        {:h (+ i j)})
      (reg-resolver ::i
        []
        {:i 5})
      (reg-resolver ::j
        []
        {:j 10})
      (reg-resolver ::k
        [{:keys [l]}]
        {:k (inc l)})
      (reg-resolver ::l
        [{:keys [m n]}]
        {:l (+ m n)})
      (reg-resolver ::m
        []
        {:m 5})
      (reg-resolver ::n
        []
        {:n 10})))
