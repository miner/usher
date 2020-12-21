(ns miner.cusher
  (:require
   clojure.pprint
   [miner.bitset :as bs]
   [clojure.data.int-map :as i]
   [clojure.math.combinatorics :as mc]))


;;; Usher Challenge to find a good rotation for nine players on two court.
;;; - plays with the other only once, 
;;; - sits once, and 
;;; - plays against every player at least twice.


;;; http://www.durangobill.com/BridgeCyclicSolutions.html

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


;;; My solution.
;;; players labeled 0-8
;;; take advantage of bits and int-set for better performance

;;; convert two bits back to pair of indices
(defn as-pair [pbits]
  [(Long/numberOfTrailingZeros pbits)
   (- 63 (Long/numberOfLeadingZeros pbits))])

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
       (= (count (:with pstats)) 8)
       (= (count (:against pstats)) 8)
       (every? #(= % 1) (vals (:with pstats)))
       (every? #(= % 2) (vals (:against pstats)))))
  
(defn verify-stats? [stats]
  (and (= (count (keys stats)) 9)
       (every? (fn [[player pstats]] (valid-player? player pstats)) stats)))




(defn as-int-set
  ([icoll] (into (i/dense-int-set) icoll))
  ([xform coll] (into (i/dense-int-set) xform coll)))


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


;;; all possible pairing -- we know we need each one once  -- 9 players => 36 pairs
;;; encoding a pair as two bits set in a long



;;; keep track of opp as vector of player-opp coord, starts all zero
;;; should end all 2 except for self which is zero
;;; zero-based, players 0-8


(defn lazy-niners []
  (let [all-pairs (as-int-set (map #(reduce bit-set 0 %) (mc/combinations (range 9) 2)))
        opp-init (vec (repeat 9 (vec (repeat 9 0))))
        legal-games  (keep (fn [[a b]] (when (zero? (bit-and a b)) [a b]))
                           (mc/combinations all-pairs 2))
        legal-rounds  (keep (fn [[[a b] [c d]]]
                              (when (= 8 (bs/bcount (bit-or a b c d))) [a b c d]))
                            (mc/combinations legal-games 2))
        group-legal-rounds (group-by #(Long/numberOfTrailingZeros (apply bit-and-not 511 %))
                                  legal-rounds)]

   (for [a (get group-legal-rounds 0)
         :let [ua (as-int-set a)
               oppa (assign-opps opp-init a)] :when oppa

         b (get group-legal-rounds 1)
         :when (not-any? ua b)
         :let [ub (into ua b)
               oppb (assign-opps oppa b)]
         :when oppb
         
         c (get group-legal-rounds 2)
         :when (not-any? ub c)
         :let [uc (into ub c)
               oppc (assign-opps oppb c)]
         :when oppc
         
         d (get group-legal-rounds 3)
         :when (not-any? uc d)
         :let [ud (into uc d)
               oppd (assign-opps oppc d)]
         :when oppd

         e (get group-legal-rounds 4)
         :when (not-any? ud e)
         :let [ue (into ud e)
               oppe (assign-opps oppd e)]
         :when oppe

         f (get group-legal-rounds 5)
         :when (not-any? ue f)
         :let [uf (into ue f)
               oppf (assign-opps oppe f)]
         :when oppf

         g (get group-legal-rounds 6)
         :when (not-any? uf g)
         :let [ug (into uf g)
               oppg (assign-opps oppf g)]
         :when oppg
         
         h (get group-legal-rounds 7)
         :when (not-any? ug h)
         :let [uh (into ug h)
               opph (assign-opps oppg h)]
         :when opph
         
         i (get group-legal-rounds 8)
         :when (not-any? uh i)
         :when (assign-opps opph i)]

     [a b c d e f g h i])))

;; about 6.5 sec on my iMac
(defn niner [] (first (lazy-niners)))


;;; one-based for display
(defn pair-str [pbits]
  (str (inc (Long/numberOfTrailingZeros (Long/lowestOneBit pbits))) "+"
       (inc (Long/numberOfTrailingZeros (Long/highestOneBit pbits)))))

(defn print-sched [niner]
  (println "Bye   Court 1        Court 2")
  (doseq [[a b c d i] (map-indexed #(conj %2 %) niner)]
    (println (inc i) "   " (pair-str a) "vs" (pair-str b)
             "   " (pair-str c) "vs" (pair-str d)))
  (println))



;; not sure how many solutions, but at least 20.  100 was taking to long so I aborted


#_ (every? #(verify-stats? (stats %)) (take 20 (niner-all)))


;;; SEM FIX ME -- write a macro that generates the FOR loop for N rounds given
;;; group-legal-rounds
;;;
;;; Maybe rewrite whole thing and generate rounds on the fly since it's only needed once
;;; A lot of this work is now done at load time.

