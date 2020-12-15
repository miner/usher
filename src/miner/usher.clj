(ns miner.usher
  (:require
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

(def inc0 (fnil inc 0))

(defn inc-stat [stats keypath]
  (update-in stats keypath inc0))


(defn add-game-stats [stats [a b c d]]
  (reduce inc-stat stats
          [[a :north] [b :north] [c :south] [d :south]
           [a :with b] [a :against c] [a :against d]
           [b :with a] [b :against c] [b :against d]
           [c :with d] [c :against a] [c :against b]
           [d :with c] [d :against a] [d :against b]]))

(defn stats [rows]
  (reduce (fn [stats [round bye game1 game2]]
            (-> stats
                (inc-stat [bye :bye])
                (add-game-stats game1)
                (add-game-stats game2)))
          {}
          rows))

(defn valid-player? [player pstats]
  (and (= (:bye pstats) 1)
       (= (:north pstats) 4)
       (= (:south pstats) 4)
       (= (count (:with pstats)) 8)
       (= (count (:against pstats)) 8)
       (every? #(= % 1) (vals (:with pstats)))
       (every? #(= % 2) (vals (:against pstats)))))
  

(defn assert-player? [player pstats]
  (assert (= (:bye pstats) 1))
  (assert (= (:north pstats) 4))
  (assert (= (:south pstats) 4))
  (assert (= (count (:with pstats)) 8))
  (assert (= (count (:against pstats)) 8))
  (assert (every? #(= % 1) (vals (:with pstats))))
  (assert (every? #(= % 2) (vals (:against pstats))))
  true)



(defn verify-stats? [stats]
  (and (= (set (keys stats)) #{:A :B :C :D :E :F :G :H :I})
       (every? (fn [[player pstats]] (valid-player? player pstats)) stats)))


#_
(verify-stats? (stats nine-sol-raw))


#_
 (map (juxt #(keyword (str (char (+ % 97)))) inc) (range 9))
 ;;=> ([:a 1] [:b 2] [:c 3] [:d 4] [:e 5] [:f 6] [:g 7] [:h 8] [:i 9])

 #_
 {:round 1
  :court 1
  :ateam [:B :C]
  :bteam [:D :E]
  :bye :A}




;; to work with Tarantella we need binary constraints
;; N number of players
;; 4 per court
;; N rounds
;; (rem N 4) get bye per round

(defn needed-courts [n]
  (quot n 4))

(defn bye-size [n]
  (rem n 4))


;; round player court

;; for easy reference
(require '[clojure.math.combinatorics :as mc])

;;; all possible pairing -- we know we need each one once  -- 9 players => 36 pairs
(def pairings (mapv set (mc/combinations (range 1 10) 2)))

;; given a player number, we know the other allowed pairs -- 28 per player
(def outpairings
  (into {}
        (for [a (range 1 10)]
          [a (set (remove #(get % a) pairings))])))

(def inpairings
  (into {}
        (for [a (range 1 10)]
          [a (set (for [b (range 1 10) :when (not= a b)] #{a b}))])))

;; for nine players, 21 outpairs per pair
(defn outpairs [pair]
  (apply s/intersection (map #(get outpairings %) pair)))

(def poutpairs  (zipmap pairings (map outpairs pairings)))


;;; SEM other idea: nine players, nine bits -- maybe bit patterns would be faster


(def s9 #{1 2 3 4 5 6 7 8 9})

(defn all-nine? [bye pairsets]
  (= s9 (apply s/union #{bye} (map set pairsets))))

(defn matchups [bye pairsets]
  (when (all-nine? bye pairsets)
    (let [[a b c d] pairsets
          used (set pairsets)]
    (list (conj (vec pairsets) used)
          [b c a d used]))))


;;; BUT need to filter pairs that overlap!  Might be easier as bits




(defn extend-court-assignment [assignment bye]
  (let [used (peek assignment)
        prev (pop assignment)]
    (into prev
          (mapcat #(matchups bye %))
          (mc/combinations (s/difference (outpairings bye) used) 4))))


;; (defn generate-sched []
;;   (reduce (fn [res bye]
;;             (into res
;;                 (assoc bye (generate-court-assignments (:used res) bye))
;;                 (assoc :used  WRONG need to append next round to each of the previous
;;              )
;;             [[#{}]]
;;             (range 1 10)))
;; 
