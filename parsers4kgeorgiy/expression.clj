(use 'clojure.string)

;; common part
(defn- fix-clojure-bad-div [f & args] (/ (double f) (apply * args)))
(defn abs [x] (if (neg? x) (- x) x))

;; functional
(defn constant [v] (fn [& args] v))
(defn variable [n] (fn [col] (get col n)))

(defn operator
  [func f-operands-col]
  (fn [& args]
    (apply func (mapv (fn [x] (apply x args)) f-operands-col))))


(defn add [& args] (operator + args))
(defn negate [& args] (operator - args))
(defn subtract [& args] (operator - args))
(defn multiply [& args] (operator * args))
(defn divide [& args] (operator fix-clojure-bad-div args))

(defn min [& args] (fn [& inner-args] (apply clojure.core/min (mapv #(apply % inner-args) args))))
(defn max [& args] (fn [& inner-args] (apply clojure.core/max (mapv #(apply % inner-args) args))))

(def ^:private global-environment {"+" add "-" subtract "*" multiply "/" divide "negate" negate "max" max "min" min})

(defn- fetch-substr-impl
  [s func]
  (if (and (not-empty s) (func (first s)))
    (+ 1 (fetch-substr-impl (subs s 1) func))
    0))
(defn fetch-substr
  [s func]
  (let [len (fetch-substr-impl s func)]
  [(subs s 0 len) (triml (subs s len))]))

(defprotocol ParserProperties
  (get-global-names [this])
  (get-variable-provider [this])
  (get-constant-provider [this])
  (provide-clojure-call [this col]))
(defprotocol Parser
  (name-to-lang [this n])
  (parse-name [this s])
  (parse-constant [this s])
  (parse-value [this s])
  (parse-values [this s])
  (parse-clojure [this s])
  (parse-program [this s]))

(def DefaultParserImplementation
  {:name-to-lang (fn [this n]
    (get (get-global-names this) n ((get-variable-provider this) n)))
   :parse-name (fn [this s]
    (let [[nam tail] (fetch-substr s #(and (not (= \) %)) (not (Character/isWhitespace %))))]
    (if (= "" nam)
      [nil tail]
      [(name-to-lang this nam) tail])))
   :parse-constant (fn [this s]
     (let [numb (re-find #"^([+\-]?\d+(\.\d+)?)(\s|\)|$)" s)]
      (if (> 2 (count numb))
        [nil s]
        [((get-constant-provider this) (read-string (nth numb 1))) (triml (subs s (count (nth numb 1))))])))
   :parse-clojure (fn [this s]
    (let [f (first s)]
    (if (not= \( f)
      [nil s]
      (let [[v o] (parse-values this (triml (subs s 1)))]
      (if (empty? v)
        (throw (Exception. "Empty brackets"))
        (if (not= \) (first o))
          (throw (Exception. "Wrong ()"))
          [(provide-clojure-call this v) (triml (subs o 1))]))))))
   :parse-value (fn [this s]
    (first (filter #(not= (first %) nil) (map #(% this s)
      [parse-constant
       parse-clojure
       parse-name]))))
   :parse-values (fn [this s]
    (let [[v t] (parse-value this s)]
    (if (nil? v)
      [nil s]
      (let [[rv rt] (parse-values this t)]
      [(concat [v] rv) rt]))))
   :parse-program (fn [this s]
    (let [[value other] (parse-value this (trim s))]
    (if (= value nil)
      (throw (Exception. "Can't parse value at the beginning of the string"))
      (if (not= other "")
        (throw (Exception. (str "Unreachable tokens: `" other "`")))
        value))))})

(defn prefix-clojure-maker [col] (let [[[f] res] (split-at 1 col)] (apply f res)))

(deftype FunctionalParser [global-environment]
  ParserProperties
    (get-global-names [this] global-environment)
    (get-constant-provider [this] constant)
    (get-variable-provider [this] variable)
    (provide-clojure-call [this col] (prefix-clojure-maker col)))

(extend FunctionalParser Parser DefaultParserImplementation)

(defn parseFunction [s] (parse-program (FunctionalParser. {"+" add "-" subtract "*" multiply "/" divide "negate" negate "max" max "min" min}) s))

;; object
; no support for &
(defprotocol ^:private Expression
  (evaluate [this col])
  (diff [this v])
  (toStringInfix [this])
  (toStringSuffix [this]))

(defprotocol ^:private Operator
  (getFunc [this])
  (getFuncOperands [this])
  (getOperatorSign [this])
  (diffImpl [this col]))

(defn- evaluateOperator
  [this col]
  {:pre [(every? #(satisfies? Expression %) (getFuncOperands this))]}
  (apply (getFunc this) (mapv #(evaluate % col) (getFuncOperands this))))
(defn- diffOperator
  [this v]
  (diffImpl this (mapv #(diff % v) (getFuncOperands this))))
(defn- operatorToString
  [this]
  (str "(" (getOperatorSign this) (reduce (fn [acc c] (str acc " " (.toString c))) "" (getFuncOperands this)) ")"))
(defn operatorToStringSuffix
  [this]
  (str "(" (reduce (fn [acc c] (str acc (toStringSuffix c) " ")) "" (getFuncOperands this)) (getOperatorSign this) ")"))
(defn operatorToStringInfix
  [this]
  {:pre [(= 2 (count (getFuncOperands this)))]}
  (let [ops (getFuncOperands this)]
    (str "(" (toStringInfix (first ops)) " " (getOperatorSign this) " " (toStringInfix (last ops)) ")")))

(def ^:private operatorExpressionImpl {:evaluate evaluateOperator :diff diffOperator :toStringSuffix operatorToStringSuffix :toStringInfix operatorToStringInfix})

(deftype ^:private CConstant [c]
  Expression
    (evaluate [this args] c)
    (diff [this v] (CConstant. 0))
    (toStringInfix [this] (.toString this))
    (toStringSuffix [this] (.toString this))
  Object
    (toString [this] (format "%.1f" (double c))))
(def EulerO (CConstant. Math/E))

(deftype ^:private CVariable [nam]
  Expression
    (evaluate [this args] (get args nam))
    (diff [this v] (if (= nam v) (CConstant. 1.0) (CConstant. 0.0)))
    (toStringInfix [this] (.toString this))
    (toStringSuffix [this] (.toString this))
  Object
    (toString [this] nam))

(deftype ^:private CAdd [f-operands]
  Operator
    (getFunc [this] +)
    (getOperatorSign [this] "+")
    (getFuncOperands [this] f-operands)
    (diffImpl [this col] (CAdd. col))
  Object
    (toString [this] (operatorToString this)))
(deftype ^:private CSubtract [f-operands]
  Operator
    (getFunc [this] -)
    (getOperatorSign [this] "-")
    (getFuncOperands [this] f-operands)
    (diffImpl [this col] (CSubtract. col))
  Object
    (toString [this] (operatorToString this)))
(deftype ^:private CNegate [f-operands]
  Operator
    (getFunc [this] -)
    (getOperatorSign [this] "negate")
    (getFuncOperands [this] f-operands)
    (diffImpl [this col] (CSubtract. col))
  Object
    (toString [this] (operatorToString this)))
(deftype ^:private CMultiply [f-operands]
  Operator
    (getFunc [this] *)
    (getOperatorSign [this] "*")
    (getFuncOperands [this] f-operands)
    (diffImpl [this col]
      (CAdd.
        [(CMultiply. [(nth col 1) (nth f-operands 0)])
         (CMultiply. [(nth col 0) (nth f-operands 1)])]))
  Object
    (toString [this] (operatorToString this)))
(deftype ^:private CDivide [f-operands]
  Operator
    (getFunc [this] fix-clojure-bad-div)
    (getOperatorSign [this] "/")
    (getFuncOperands [this] f-operands)
    (diffImpl [this col]
      (CDivide.
        [(CSubtract.
           [(CMultiply. [(nth col 0) (nth f-operands 1)])
            (CMultiply. [(nth col 1) (nth f-operands 0)])])
         (CMultiply. [(nth f-operands 1) (nth f-operands 1)])]))
  Object
    (toString [this] (operatorToString this)))
(deftype ^:private CLg [f-operands]
  Operator
    (getFunc [this] #(/ (Math/log (abs %2)) (Math/log (abs %1))))
    (getOperatorSign [this] "lg")
    (getFuncOperands [this] {:pre [(= 2 (count f-operands))]} f-operands)
    (diffImpl [this col] (CSubtract. [(CDivide. [(nth col 1)
                                                 (nth f-operands 1) (CLg. [EulerO (nth f-operands 0)])])
                                      (CDivide. [(CMultiply. [(nth col 0) this])
                                                 (nth f-operands 0) (CLg. [EulerO (nth f-operands 0)])])]))
  Object
    (toString [this] (operatorToString this)))
(deftype ^:private CPw [f-operands]
  Operator
    (getFunc [this] #(Math/pow %1 %2))
    (getOperatorSign [this] "pw")
    (getFuncOperands [this] {:pre [(= 2 (count f-operands))]} f-operands)
    (diffImpl [this col] (CMultiply. [this (CAdd. [(CMultiply. [(nth col 1) (CLg. [EulerO (nth f-operands 0)])])
                                                   (CDivide. [(CMultiply. [(nth f-operands 1) (nth col 0)])
                                                              (nth f-operands 0)])])]))
  Object
    (toString [this] (operatorToString this)))

(defn- get-bit-operation-applyer
  [func]
  (fn [& args]
    (Double/longBitsToDouble
      (reduce
        func
        (mapv #(Double/doubleToLongBits %) args)))))

;; 12 modification
(deftype ^:private CXor [f-operands]
  Operator
    (getFunc [this] (get-bit-operation-applyer bit-xor))
    (getOperatorSign [this] "^")
    (getFuncOperands [this] f-operands)
      Object
    (toString [this] (operatorToString this)))
(deftype ^:private COr [f-operands]
  Operator
    (getFunc [this] (get-bit-operation-applyer bit-or))
    (getOperatorSign [this] "|")
    (getFuncOperands [this] f-operands)
      Object
    (toString [this] (operatorToString this)))
(deftype ^:private CAnd [f-operands]
  Operator
    (getFunc [this] (get-bit-operation-applyer bit-and))
    (getOperatorSign [this] "&")
    (getFuncOperands [this] f-operands)
      Object
    (toString [this] (operatorToString this)))
(defn Xor [& args] (CXor. args))
(defn Or [& args] (COr. args))
(defn And [& args] (CAnd. args))

;; end 12 of modification

(doseq [clazz [CAdd, CSubtract, CMultiply, CDivide, CPw, CLg, CXor, COr, CAnd]]
  (extend clazz
    Expression
      operatorExpressionImpl))

(doseq [clazz [CNegate]]
  (extend clazz
    Expression
      (merge operatorExpressionImpl {:toStringInfix (fn [this] {:pre [(= 1 (count (getFuncOperands this)))]} (str (getOperatorSign this) "(" (toStringInfix (first (getFuncOperands this))) ")"))})))

(def Constant #(CConstant. %))
(def Variable #(CVariable. %))
(defn Add [& args] (CAdd. args))
(defn Subtract [& args] (CSubtract. args))
(defn Negate [& args] (CNegate. args))
(defn Multiply [& args] (CMultiply. args))
(defn Divide [& args] (CDivide. args))
(defn Pw [& args] (CPw. args))
(defn Lg [& args] (CLg. args))

(deftype ObjectParser [global-environment]
  ParserProperties
    (get-global-names [this] global-environment)
    (get-constant-provider [this] Constant)
    (get-variable-provider [this] Variable)
    (provide-clojure-call [this col] (prefix-clojure-maker col)))
(extend ObjectParser Parser DefaultParserImplementation)

(defn parseObject [s] (parse-program (ObjectParser. {"+" Add "-" Subtract "*" Multiply "/" Divide "negate" Negate "pw" Pw "lg" Lg}) s))

(def toString #(.toString %))

;; tabulator
(def infix-priorities [{"^" Xor} {"|" Or} {"&" And} {"+" Add "-" Subtract} {"*" Multiply "/" Divide}])
(def all-infix-operators (reduce merge infix-priorities))
(defn- name-to-lang-tab [n] (get all-infix-operators n (Variable n)))


(defn -return [value tail] {:value value :tail tail})
(def -valid? boolean)
(def -value :value)
(def -tail :tail)
(defn _show [result]
  (if (-valid? result) (str "-> " (pr-str (-value result)) "\t\t|\t" (pr-str (apply str (-tail result))))
    "!"))
(defn tabulate [parser inputs]
  (run! (fn [input] (printf "    %-10s %s\n" (pr-str input) (_show (parser input)))) inputs))

(defn _empty [value] (partial -return value))
(defn _char [p]
  (fn [[c & cs]]
    (if (and c (p c)) (-return c cs))))
(defn _map [f result]
  (if (-valid? result)
    (-return (f (-value result)) (-tail result))))

(defn _combine [f a b]
  (fn [str]
    (let [ar ((force a) str)]
      (if (-valid? ar)
        (_map (partial f (-value ar))
        ((force b) (-tail ar)))))))
(defn _either [a b]
  (fn [str]
    (let [ar ((force a) str)]
      (if (-valid? ar) ar ((force b) str)))))

(defn _parser [p]
  (fn [input]
    (-value ((_combine (fn [v _] v) p (_char #{\u0000})) (str input \u0000)))))

(defn +char [chars] (_char (set chars)))
(defn +char-not [chars] (_char (comp not (set chars))))
(defn +map [f parser] (comp (partial _map f) parser))
(def +parser _parser)

(def +ignore (partial +map (constantly 'ignore)))
(defn iconj [coll value]
  (if (= value 'ignore) coll (conj coll value)))
(defn +seq [& ps]
  (reduce (partial _combine iconj) (_empty []) ps))
(defn +seqf [f & ps] (+map (partial apply f) (apply +seq ps)))
(defn +seqn [n & ps] (apply +seqf (fn [& vs] (nth vs n)) ps))

(defn +or [p & ps]
  (reduce _either p ps))
(defn +if [c pit pif] (if c pit pif))
(defn +opt [p]
  (+or p (_empty 'ignore)))
(defn +star [p]
  (letfn [(rec [] (+or (+seqf cons p (delay (rec))) (_empty ())))] (rec)))
(defn +plus [p] (+seqf cons p (+star p)))
(defn +str [p] (+map (partial apply str) p))
(defn +strseq [& p] (+str (apply +seq p)))
(defn +string [s] (+str (apply +seq (mapv (fn [c] (+char (str c))) s))))

(def *digit (+char "0123456789"))
(def *digits (+str (+plus *digit)))
(def *number (+map #(CConstant. (read-string %)) (+strseq (+opt (+char "+-")) *digits (+opt (+strseq (+char ".") *digits)))))

(def infix-operators (reduce concat (mapv keys infix-priorities)))
(def infix-unary-operators {"negate" Negate})

(def *all-chars (mapv char (range 32 128)))
(apply str *all-chars)
(def *letter (+char (apply str (filter #(Character/isLetter %) *all-chars))))
(def *identifier (+map name-to-lang-tab (apply +or (+str (+seqf cons *letter (+star (+or *letter *digit)))) (mapv +string infix-operators))))

(def *ws (+ignore (+star (+char " \t\n\r"))))
(declare *value)
(defn postfix-clojure-maker [col] (let [[res [f]] (split-at (- (count col) 1) col)] (apply f res)))
(defn tabulator-make-cloj [col] (postfix-clojure-maker col))
;; delay defenitions
(defn *clojure [input] ((+map #(tabulator-make-cloj (mapv first (second %))) (+seq *ws (+char "(") (+plus (+seq *ws *value )) *ws (+char ")"))) input))
(def *value (+or *clojure *number *identifier))

(defn parseObjectSuffix [s]
  (let [x ((+seq *ws *value *ws) s)]
    (cond
      (nil? x) (throw (Exception. "Can't parse value at the beginning of the string"))
      (not (nil? (:tail x))) (throw (Exception. "Unreachable tokens"))
      :else (first (:value x)))))

(declare *infix-op)
(defn *infix-atom [input] ((+or
  *number
  *identifier
  (+map second (+seq
    *ws
    (+string "(")
    *ws
    (*infix-op 0)
    *ws
    (+string ")")))) input))
(defn *infix-superatom [input]
  ((+or
    (+map (fn [[f ar]] ((get infix-unary-operators f) ar)) (+seq
      *ws
      (apply +or (concat (mapv +string (keys infix-unary-operators))))
      *ws
      *infix-superatom))
    *infix-atom) input))
(defn *infix-op-deeper [depth] (*infix-op (+ depth 1)))
(defn *infix-op-op
  [depth]
  (let [cur-depth (nth infix-priorities depth)]
  (+map
    #(get cur-depth  %)
    (apply +or (mapv +string (keys cur-depth))))))
(defn *infix-unroll-op [[f col]] (reduce (fn [l [op-r r-r]] (op-r l r-r)) f col))
(defn *infix-op [depth] (if (<= (count infix-priorities) depth)
  *infix-superatom
  (+map *infix-unroll-op (+seq
    *ws
    (*infix-op-deeper depth)
    (+star (+seq
      *ws
      (*infix-op-op depth)
      *ws
      (*infix-op-deeper depth)))))))
(defn parseObjectInfix [s] (:value ((*infix-op 0) s)))

