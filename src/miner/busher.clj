(ns miner.busher
  (:require
   clojure.pprint
   [miner.bitset :as bs]
   [clojure.data.int-map :as i]
   [clojure.set :as s]
   [clojure.math.combinatorics :as c]
   [tarantella.core :as t]))

;;; Challenge from Rob Usher
;;;
;;; It's remarkable I can't find a balanced round-robin for 9 & 10 players in doubles teams.
;;; Every example on the internet does NOT balance competition.  I need one where each player:
;;;
;;; - plays with the other only once, 
;;; - sits once, and 
;;; - plays against every player at least twice.


;;; http://www.durangobill.com/BridgeCyclicSolutions.html

;;; sounds like a good opportunity for Knuth's Dancing Links
;;; See Mark Engleberg's Tarantella:
;;; https://github.com/Engelberg/tarantella


;;; http://www.jdawiseman.com/papers/tournaments/individual-pairs/ip-pure_09.html
;;; 9-player round-robin on two courts, players A-I

"   
  Bye    i       ii    
 1 A  B+C:D+G  E+I:F+H 
 2 B  C+A:E+H  F+G:D+I 
 3 C  A+B:F+I  D+H:E+G 
 4 D  E+F:G+A  H+C:I+B 
 5 E  F+D:H+B  I+A:G+C 
 6 F  D+E:I+C  G+B:H+A 
 7 G  H+I:A+D  B+F:C+E 
 8 H  I+G:B+E  C+D:A+F 
 9 I  G+H:C+F  A+E:B+D
"


(def nine-sol-raw
  [[1 :A  [:B :C :D :G]  [:E :I :F :H]]
   [2 :B  [:C :A :E :H]  [:F :G :D :I]]
   [3 :C  [:A :B :F :I]  [:D :H :E :G]]
   [4 :D  [:E :F :G :A]  [:H :C :I :B]]
   [5 :E  [:F :D :H :B]  [:I :A :G :C]]
   [6 :F  [:D :E :I :C]  [:G :B :H :A]]
   [7 :G  [:H :I :A :D]  [:B :F :C :E]]
   [8 :H  [:I :G :B :E]  [:C :D :A :F]]
   [9 :I  [:G :H :C :F]  [:A :E :B :D]]])


(defn convert-to-knum [nine-sol-raw]
  (let [knum (fn [k] (- (long (first (name k))) (dec (long \A))))]
    (mapv (fn [[r b g1 g2]] [(mapv knum g1) (mapv knum g2)]) nine-sol-raw)))

;;; players 1-9 no 0
(def knum9 [[[2 3 4 7] [5 9 6 8]]
            [[3 1 5 8] [6 7 4 9]]
            [[1 2 6 9] [4 8 5 7]]
            [[5 6 7 1] [8 3 9 2]]
            [[6 4 8 2] [9 1 7 3]]
            [[4 5 9 3] [7 2 8 1]]
            [[8 9 1 4] [2 6 3 5]]
            [[9 7 2 5] [3 4 1 6]]
            [[7 8 3 6] [1 5 2 4]]])




;;; Zero-based bit notation is vector of vector of longs where each long has two bits set
;;; for players 0-8.  A round is a vector of 4 longs, representing two pairs of opponents.
;;; [[A B C D] ...] represents pair A vs. B and C vs. D.  Altogether each round should be 8
;;; unique bits, with bye matching round index (0-8).

;; zero-based bits
(defn convert-to-bits [nine-sol-raw]
  (let [knum (fn [k] (- (long (first (name k))) (long \A)))]
    (mapv (fn [[r b g1 g2]]
            (->> (sequence (comp (map knum) (map #(bit-set 0 %))) (concat g1 g2))
                (partition 2)
                (mapv (fn [[a b]] (bit-or a b)))))
          nine-sol-raw)))

(defn verify-bits? [bits9]
  (every? zero? (map-indexed (fn [i r] (reduce bit-and-not (bit-clear 511 i) r)) bits9)))

;; players 0-8 in pairs of bits
(def bits9 [[6 72 272 160]
            [5 144 96 264]
            [3 288 136 80]
            [48 65 132 258]
            [40 130 257 68]
            [24 260 66 129]
            [384 9 34 20]
            [320 18 12 33]
            [192 36 17 10]])


(defn as-pair [pbits]
  [(Long/numberOfTrailingZeros (Long/highestOneBit pbits))
   (Long/numberOfTrailingZeros (Long/lowestOneBit pbits))])

;; should be faster than (bs/bindices pbits)



(def inc0 (fnil inc 0))

(defn inc-stat [stats keypath]
  (update-in stats keypath inc0))


(defn add-game-stats [stats [a b c d]]
  (reduce inc-stat stats
          [[a :with b] [a :against c] [a :against d]
           [b :with a] [b :against c] [b :against d]
           [c :with d] [c :against a] [c :against b]
           [d :with c] [d :against a] [d :against b]]))

(defn stats [rows]
  (reduce-kv (fn [stats bye [a b c d]]
               (-> stats
                   (inc-stat [bye :bye])
                   (add-game-stats (into (as-pair a) (as-pair b)))
                   (add-game-stats (into (as-pair c) (as-pair d)))))
          {}
          rows))

(defn valid-player? [player pstats]
  (and (= (:bye pstats) 1)
       #_ (= (:north pstats) 4)
       #_ (= (:south pstats) 4)
       (= (count (:with pstats)) 8)
       (= (count (:against pstats)) 8)
       (every? #(= % 1) (vals (:with pstats)))
       (every? #(= % 2) (vals (:against pstats)))))
  

(defn assert-player? [player pstats]
  (assert (= (:bye pstats) 1))
  #_ (assert (= (:north pstats) 4))
  #_ (assert (= (:south pstats) 4))
  (assert (= (count (:with pstats)) 8))
  (assert (= (count (:against pstats)) 8))
  (assert (every? #(= % 1) (vals (:with pstats))))
  (assert (every? #(= % 2) (vals (:against pstats))))
  true)


;; #{:A :B :C :D :E :F :G :H :I}

(defn verify-stats? [stats]
  (and (= (count (keys stats)) 9)
       (every? (fn [[player pstats]] (valid-player? player pstats)) stats)))


#_
(verify-stats? (stats bits9))





(defn as-int-set [icoll]
  (into (i/dense-int-set) icoll))







;; to work with Tarantella we need binary constraints
;; N number of players
;; 4 per court
;; N rounds
;; (rem N 4) get bye per round
;;;;;; NEED TO THINK MORE ABOUT THIS
;;;;;;  maybe search for allowed pairs first, then verify other stats????






;; for easy reference
(require '[clojure.math.combinatorics :as mc])

;;; all possible pairing -- we know we need each one once  -- 9 players => 36 pairs
(def pairings (mapv #(reduce bit-set 0 %) (mc/combinations (range 9) 2)))

(def all-pairs (into (s/dense-int-set) pairings))

;; given a player number, we know the other allowed pairs -- 28 per player
(def outpairings
  (into (i/int-map)
        (for [a (range 9)]
          [a (as-int-set (remove #(bit-test % a) pairings))])))

(def inpairings
  (into (i/int-map)
        (for [a (range 9)]
          [a (as-int-set (for [b (range 9) :when (not= a b)] (-> 0 (bit-set a) (bit-set b))))])))

;; for nine players, 21 outpairs per pair
(defn outpairs [pair]
  (apply i/intersection (map #(get outpairings %) (as-pair pair))))

(def poutpairs (into (i/int-map) (zipmap pairings (map outpairs pairings))))






;;; another way to start from pairs
;;; choose one pair, choose second pair from pair-1 outpairs (27)
;;; keep track of "used" pairs as you go to cut down possibles
;;; keep track of opponent count per player as you go -- two allowed
;;; that should help prune pairs in games
;;; need to back track when stuck
;;; state is vector of games (two pairs each), total used pairs, opp map




;;; Thinking some more 
;;;  9 choose 8

;;; how many ways of arranging 8?  9 subs for one of them for each round
;;; probably better to start with pairs
;;; add constraint that init pair limits next, then add another one at a time
;;; backtrack to get all possible arrangements for a single round
;;;


;;; keep track of opp as vector of player-opp coord, starts all zero
;;; should end all 2 except for self which is zero
;;; zero-based, players 0-8
(def opp-init (vec (repeat 9 (vec (repeat 9 0)))))

;;; playing once with each other is guaranteed by initial pairs

;; wrap f2 so that a nil/false result short-circuits the calling `reduce`, thus returning
;; nil
;; a bit ugly
(defn whilst [f2]
  (fn
    ([] (f2))
    ([acc] (f2 acc))
    ([acc item]
     (if-not acc
       (reduced nil)
       (if-let [res (f2 acc item)]
         res
         (reduced nil))))))

(defn inc-max2 [opps coord]
  ;;(println "inc-max2" opps coord)
  (when (and opps (< (get-in opps coord) 2))
    (update-in opps coord inc)))

(defn inc-opp [opps a b]
  (let [[a1 a2] (as-pair a)
        [b1 b2] (as-pair b)]
    (reduce (whilst inc-max2) opps [[a1 b1] [a1 b2] [a2 b1] [a2 b2]
                                    [b1 a1] [b1 a2] [b2 a1] [b2 a2]])))
    
(defn assign-opps [opps [a b c d]]
  (some-> opps
      (inc-opp a b)
      (inc-opp c d)))




;;; FIXME do you really need to remix games?
(defn confirm-matchups [bye pairsets assignment]
  (when (all-nine? bye pairsets)
    (let [prev (:assigned assignment)
          used (into (:used assignment) pairsets)
          opp (assign-opps (:opp assignment) pairsets)
          [a b c d] pairsets
          pairsets2 [b c a d]
          opp2 (assign-opps (:opp assignment) pairsets2)]
      (cond (and opp opp2) 
                (list {:used used
                       :opp opp
                       :assigned (into prev pairsets)}
                      {:used used
                       :opp opp2
                       :assigned (into prev pairsets2)})
            opp (list {:used used
                       :opp opp
                       :assigned (into prev pairsets)})
            opp2 (list {:used used
                        :opp opp2
                        :assigned (into prev pairsets2)})
            :else nil))))


(defn extend-assignment [assignment bye]
  (mapcat #(confirm-matchups bye % assignment)
          (mc/combinations (s/difference (outpairings bye) (:used assignment)) 4)))



;;; SEM IDEA: vector of bitpairs
;;; tarantella for layout of 0-35 bitpairs
;;; figure out additional constraints on individual
;;; each row could be one pair (36) on one court side (four)
;;; no overlapping pairs (by construction)
;;; That is, write a program to generat the right constraints, then let taran solve.
;;; Might be partial and need fix up.


(defn dfgen
  ([] (dfgen 9))
  ([limit]
   (loop [stack [{:available all-pairs :opp opp-init :assigned []}]]
     (if-let [assignment (peek stack)]
       (let [{:keys [available opp assigned]} assignment
             bye (quot (count assigned) 4)
             candidates (s/intersection available (outpairings bye))]
         (if (>= bye limit)
           assignment
           (let [next4 (take 4 candidates)]
             )))))))
         






;;; gen9 returns first solution.  It takes a long time.  Very fast until 8, then slow for 8
;;; and 9.

(defn gen9
  ([] (gen9 9))
  ([limit]
  (loop [bye 1 assignments [{:used #{} :opp opp-init :assigned []}]]
    (if (> bye limit)
      (:assigned (first assignments))
      (if (empty? assignments)
        (println "Warning: empty assignments")
      (do
        (println)
        (println "pre Bye " bye)
        (clojure.pprint/pprint (map :assigned (take 3 assignments)))
        #_ (clojure.pprint/pprint  (take 3 assignments))
        (println "done " bye)
        (println)

        (recur (inc bye) (mapcat #(extend-assignment % bye) assignments))))))))




(defn gen-all
  ([] (gen-all 9))
  ([limit]
  (loop [bye 1 assignments [{:used #{} :opp opp-init :assigned []}]]
    (if (> bye limit)
      (map :assigned assignments)
      (if (empty? assignments)
        (println "Warning: empty assignments")
      (do
        (println)
        (println "pre Bye " bye)
        (clojure.pprint/pprint (map :assigned (take 3 assignments)))
        #_ (clojure.pprint/pprint  (take 3 assignments))
        (println "done " bye)
        (println)

        (recur (inc bye) (mapcat #(extend-assignment % bye) assignments))))))))




(def sol9
  [#{6 3} #{7 5} #{4 8} #{2 9} #{7 1} #{9 5} #{4 6} #{3 8} #{2 8} #{1 5} #{7 6} #{4 9}
   #{7 3} #{1 8} #{6 9} #{2 5} #{6 8} #{7 2} #{4 3} #{1 9} #{7 4} #{1 2} #{5 8} #{3 9}
   #{9 8} #{1 6} #{3 5} #{4 2} #{6 5} #{1 4} #{7 9} #{3 2} #{6 2} #{1 3} #{4 5} #{7 8}])


(defn convert-sol [sol]
  (mapv (fn [r gs] (into [r r] gs))
        (range 1 10)
       (->> sol
            (partition 2)
            (map (fn [pp] (into [] (mapcat seq) pp)))
            (partition 2))))



;;;; Breadth-first is too slow, too many possibilities
;;; Need a depth-first approach and quit on first solution



(comment

(require '[clojure.set :as s])
(require '[clojure.math.combinatorics :as mc])


(mc/count-combinations (range 8) 4)
70
user=> (mc/count-combinations (range 9) 8)
9


(mc/count-permutations (range 9))
362880

(take 20 (mc/permutations (range 8)))

([0 1 2 3 4 5 6 7]
 [0 1 2 3 4 5 7 6]
 [0 1 2 3 4 6 5 7]
 [0 1 2 3 4 6 7 5]
 [0 1 2 3 4 7 5 6]
 [0 1 2 3 4 7 6 5]
 [0 1 2 3 5 4 6 7]
 [0 1 2 3 5 4 7 6]
 [0 1 2 3 5 6 4 7]
 [0 1 2 3 5 6 7 4]
 [0 1 2 3 5 7 4 6]
 [0 1 2 3 5 7 6 4]
 [0 1 2 3 6 4 5 7]
 [0 1 2 3 6 4 7 5]
 [0 1 2 3 6 5 4 7]
 [0 1 2 3 6 5 7 4]
 [0 1 2 3 6 7 4 5]
 [0 1 2 3 6 7 5 4]
 [0 1 2 3 7 4 5 6]
 [0 1 2 3 7 4 6 5])


)
