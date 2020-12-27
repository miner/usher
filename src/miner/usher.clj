(ns miner.usher
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

(defn high-bit [pbits]
  (- 63 (Long/numberOfLeadingZeros pbits)))

(defn low-bit [pbits]
  (Long/numberOfTrailingZeros pbits))

;;; convert two bits back to pair of indices
(defn as-pair [pbits]
  [(low-bit pbits) (high-bit pbits)])


;; questionable -- maybe faster than nested vectors
(defn ind9 [a b]
  (+ (* a 9) b))



(def inc0 (fnil inc 0))

(defn inc-stat [stats keypath]
  (update-in stats keypath inc0))

(defn add-game-stats [stats a b c d]
  (reduce inc-stat stats
          [[a :with b] [a :against c] [a :against d]
           [b :with a] [b :against c] [b :against d]
           [c :with d] [c :against a] [c :against b]
           [d :with c] [d :against a] [d :against b]]))


(defn unique-games? [rows]
  (distinct? (mapcat (fn [[a b c d]] (list (bit-or a b) (bit-or c d))) rows)))

;; round [abcd]
(defn find-bye [[a b c d]]
  (let [bits (bit-and-not 511 a b c d)]
    (when (= (bs/bcount bits) 1)
      (bs/bmin bits))))

;;; bye is assumed not checked
(defn stats [rows]
  (reduce-kv (fn [stats bye [a b c d]]
               (-> stats
                   (inc-stat [bye :bye])
                   (add-game-stats (low-bit a) (high-bit a) (low-bit b) (high-bit b))
                   (add-game-stats (low-bit c) (high-bit c) (low-bit d) (high-bit d))))
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

(defn verify-niner? [niner]
  (and (unique-games? niner)
       (= (map find-bye niner) (range 9))
       (verify-stats? (stats niner))))


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
  (let [a1 (low-bit a)
        a2 (high-bit a)
        b1 (low-bit b)
        b2 (high-bit b)]
    (reduce (whilst inc-max2) opps [[a1 b1] [a1 b2] [a2 b1] [a2 b2]
                                    [b1 a1] [b1 a2] [b2 a1] [b2 a2]])))
    
(defn assign-opps [opps [a b c d]]
  (some-> opps
      (inc-opp a b)
      (inc-opp c d)))


;;; all possible pairing -- we know we need each one once  -- 9 players => 36 pairs
;;; encoding a pair as two bits set in a long



(defn experiment
  ([] (experiment false))
  ([flag]
   (let [all-pairs (as-int-set (for [a (range 9) :let [pbits (bit-set 0 a)]
                                     b (range (inc a) 9)]
                                 (bit-set pbits b)))
         opp-init (vec (repeat 9 (vec (repeat 9 0))))
         legal-games  (keep (fn [[a b]] (when (zero? (bit-and a b)) [a b (bit-or a b)]))
                            (mc/combinations all-pairs 2))
         legal-rounds (keep (fn [[ab cd]]
                              (when (zero? (bit-and (peek ab) (peek cd)))
                                [(nth ab 0) (nth ab 1) (nth cd 0) (nth cd 1)]))
                            (mc/combinations legal-games 2))
         group-legal-rounds (group-by #(Long/numberOfTrailingZeros (apply bit-and-not 511 %))
                                      legal-rounds)]
     (assert (= (count all-pairs) 36))
     (assert (= (sort (keys group-legal-rounds)) (range 9)))
     (assert (every? #(= 315 (count %)) (vals group-legal-rounds)))
     (if flag
       (do (println "all-pairs:" (count all-pairs))
           (println "legal-games:" (count legal-games))
           (println "legal-rounds:" (count legal-rounds) "  per bye:"
                    (quot (count legal-rounds) 9))
           (println "returning group-legal-rounds")
           group-legal-rounds)
       true))))



;; not faster with into/pop


;;; only slightly faster with bit-or keys (instead of bye)

(defn experiment2
  ([] (experiment2 false))
  ([flag]
  (let [all-pairs (as-int-set (for [a (range 9) :let [pbits (bit-set 0 a)]
                                    b (range (inc a) 9)]
                                (bit-set pbits b)))
        opp-init (vec (repeat 9 (vec (repeat 9 0))))
        legal-games  (keep (fn [[a b]] (when (zero? (bit-and a b)) [a b (bit-or a b)]))
                           (mc/combinations all-pairs 2))
        legal-rounds  (keep (fn [[ab cd]]
                              (when (zero? (bit-and (peek ab) (peek cd)))
                                [(nth ab 0) (nth ab 1) (nth cd 0) (nth cd 1)]
                                #_ (into (pop ab) (pop cd))))
                            (mc/combinations legal-games 2))
        group-legal-rounds (group-by #(apply bit-or %)
                                     legal-rounds)]
    (assert (= (count all-pairs) 36))
    (assert (= (sort (keys group-legal-rounds)) (sort (map #(bit-clear 511 %) (range 9)))))
    (assert (every? #(= 315 (count %)) (vals group-legal-rounds)))
    (if flag
      (do (println "all-pairs:" (count all-pairs))
          (println "legal-games:" (count legal-games))
          (println "legal-rounds:" (count legal-rounds) "  per bye:"
                   (quot (count legal-rounds) 9))
          (println "returning group-legal-rounds")
          group-legal-rounds)
      true))))



;;; keep track of opp as vector of player-opp coord, starts all zero
;;; should end all 2 except for self which is zero
;;; zero-based, players 0-8

;;; probably would be faster to unroll opps into single vector of 81
;;; multiply instead of as-pair

;; all-pairs was originally:
;;   (map #(reduce bit-set 0 %) (mc/combinations (range 9) 2))
;; but the new code is faster


(defn lazy-niners []
  (let [opp-init (vec (repeat 9 (vec (repeat 9 0))))
        all-pairs (as-int-set (for [a (range 9) :let [pbits (bit-set 0 a)]
                                    b (range (inc a) 9)]
                                (bit-set pbits b)))
        legal-games  (keep (fn [[a b]] (when (zero? (bit-and a b)) [a b (bit-or a b)]))
                           (mc/combinations all-pairs 2))
        legal-rounds (keep (fn [[ab cd]]
                             (when (zero? (bit-and (peek ab) (peek cd)))
                               [(nth ab 0) (nth ab 1) (nth cd 0) (nth cd 1)]))
                           (mc/combinations legal-games 2))
        group-legal-rounds (group-by #(Long/numberOfTrailingZeros (apply bit-and-not 511 %))
                                     legal-rounds)]

    (for [a (get group-legal-rounds 0)
          :let [ua (as-int-set a)]
          :let [oppa (assign-opps opp-init a)]
          :when oppa

          b (get group-legal-rounds 1)
          :when (not-any? ua b)
          :let [oppb (assign-opps oppa b)]
          :when oppb
          :let [ub (into ua b)]
          
          c (get group-legal-rounds 2)
          :when (not-any? ub c)
          :let [oppc (assign-opps oppb c)]
          :when oppc
          :let [uc (into ub c)]
          
          d (get group-legal-rounds 3)
          :when (not-any? uc d)
          :let [oppd (assign-opps oppc d)]
          :when oppd
          :let [ud (into uc d)]

          e (get group-legal-rounds 4)
          :when (not-any? ud e)
          :let [oppe (assign-opps oppd e)]
          :when oppe
          :let [ue (into ud e)]

          f (get group-legal-rounds 5)
          :when (not-any? ue f)
          :let [oppf (assign-opps oppe f)]
          :when oppf
          :let [uf (into ue f)]

          g (get group-legal-rounds 6)
          :when (not-any? uf g)
          :let [oppg (assign-opps oppf g)]
          :when oppg
          :let [ug (into uf g)]
          
          h (get group-legal-rounds 7)
          :when (not-any? ug h)
          :let [opph (assign-opps oppg h)]
          :when opph
          :let [uh (into ug h)]
          
          i (get group-legal-rounds 8)
          :when (not-any? uh i)
          :when (assign-opps opph i)]

      [a b c d e f g h i])))

;; about 6.5 sec on my iMac
(defn niner [] (first (lazy-niners)))


;;; one-based for display
(defn pair-str [pbits]
  (str (inc (Long/numberOfTrailingZeros pbits)) "+"
       (inc (Long/numberOfTrailingZeros (Long/highestOneBit pbits)))))

(defn print-sched [niner]
  (println "Bye   Court 1        Court 2")
  (doseq [[a b c d i] (map-indexed #(conj %2 %) niner)]
    (println (inc i) "   " (pair-str a) "vs" (pair-str b)
             "   " (pair-str c) "vs" (pair-str d)))
  (println))


(def expected-niner
  [[6 24 96 384] [5 160 72 272] [3 320 48 136] [17 192 34 260] [9 288 68 130]
   [12 65 144 258] [18 33 132 264] [20 257 40 66] [10 129 36 80]])


;; not sure how many solutions, but at least 20.  100 was taking to long so I aborted


#_ (every? #(verify-stats? (stats %)) (take 20 (niner-all)))


;;; SEM FIX ME -- write a macro that generates the FOR loop for N rounds given
;;; group-legal-rounds
;;;
;;; Maybe rewrite whole thing and generate rounds on the fly since it's only needed once
;;; A lot of this work is now done at load time.


#_
(time (last (take 25 (lazy-niners))))
;; "Elapsed time: 15873.597243 msecs"
;;=> [[6 24 96 384] [5 320 40 144] [3 160 80 264] [17 192 34 260] [9 288 68 130]
;;    [10 65 132 272] [20 33 136 258] [18 257 36 72] [12 129 48 66]]

(defn millis [] (.millis (java.time.Clock/systemDefaultZone)))



#_ (time (last (take 45 (lazy-niners))))
;; "Elapsed time: 68820.437288 msecs"
;; => [[6 24 96 384] [12 288 17 192] [34 144 65 264] [5 160 18 320] [33 258 72 132]
;;     [3 68 136 272] [9 48 130 260] [20 257 40 66] [10 129 36 80]]








;;; https://math.stackexchange.com/questions/2237894/in-how-many-ways-can-you-arrange-4n-tennis-players-into-doubles-matches

(defn fact [n]
  (reduce * (range 1 (inc n))))

(defn ** [a b]
  (reduce * (repeat b a)))

(defn count-arrangements-for-courts [n]
  ;; n courts
  (/ (fact (* 4 n))
     (* (fact n) (** 2 (* 3 n)))))
  
  
#_ (count-arrangements-for-courts 2)
;;=>  315
;; That's exactly how many legal rounds we get per bye for our nine-player solution. Hmmm...
;; Could we just enumerate those and substitute for the bye player?


;; (mc/count-combinations (range 9) 2)  => 36
;; 36 pairs to start from 9 players
;;

;; (mc/count-combinations (range 36) 2)  => 630
;; legal games 630

;; that's double 315 rounds per bye, but why exactly?  A round is two games
;;
;;  WRONG REASON but we don't care about order of teams so we only get half the combinations
;; for legal games.  



(defn BADnormalize [rounds]
  (sort (map (fn [[a b c d]] (vector (bit-or a b) (bit-or c d))) rounds)))

;;; wrong on bit-test -clear because old is still there--- but sub was guaranteed not there???
;;; need to rotate all bits (I think)

(defn BADrenormalize [rounds player sub]
  (let [gsub (fn [a b]
               (let [g (bit-or a b)]
                 (if (bit-test g player)
                   (-> g (bit-clear player) (bit-set sub))
                   g)))]
    (sort (map (fn [[a b c d]] (vector (sort (list (gsub a b) (gsub c d))))) rounds))))

;;;  renormalize does not seem to work so maybe there is a deeper problem with the original
;;;  generation



(defn renormalize [rounds player sub]
  (let [gsub (fn [p]
               (if (bit-test p player)
                   (-> p (bit-clear player) (bit-set sub))
                   p))]
    (sort (map (fn [p4] (mapv gsub p4)) rounds))))


;; (mc/count-combinations (range 36) 2)  ==> 630 legal games
;;   divide by two games per round  ==> 315 rounds  ????  but does that cover all mixes?


;;; To use Tarantella we need vector of bits for each possibility.  Solution is subset that
;;; covers all bits.

;;; 9 players, 9 rounds, 1 bye + 8 players per round, 2games per round = 18 games, 2 sides
;;; per game = 36 sides



;;; considering per round, 1 bye, 8 players -- should be symmetric for other rounds
;;; probably needs a rotation of players, not just a substitution
;;; (mc/count-combinations (range 8) 2) => 28
;;; exp8 gives 315 rounds

(defn exp8
  ([] (exp8 true))
  ([flag]
   (let [all-pairs (as-int-set (for [a (range 8) :let [pbits (bit-set 0 a)]
                                     b (range (inc a) 8)]
                                 (bit-set pbits b)))
         opp-init (vec (repeat 8 (vec (repeat 8 0))))
         legal-games  (keep (fn [[a b]] (when (zero? (bit-and a b)) [a b (bit-or a b)]))
                            (mc/combinations all-pairs 2))
         legal-rounds (keep (fn [[ab cd]]
                              (when (zero? (bit-and (peek ab) (peek cd)))
                                [(nth ab 0) (nth ab 1) (nth cd 0) (nth cd 1)]))
                            (mc/combinations legal-games 2))]

     (if flag
       (do (println "8 all-pairs:" (count all-pairs))
           (println "8 legal-games:" (count legal-games))
           (println "8 legal-rounds:" (count legal-rounds))
           (count legal-rounds))
       true))))



;;; 43210  rot 2
;;; 21043

;; rotate pos to left
(defn rotate-bits [width bits n]
  (bit-or (bit-and (bit-shift-left bits n) (dec (bit-set 0 width)))
          (bit-and (unsigned-bit-shift-right bits (- width n)) (dec (bit-set 0 n)))))

  
