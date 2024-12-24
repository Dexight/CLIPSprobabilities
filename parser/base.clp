;========================================================================
; Этот блок реализует логику обмена информацией с графической оболочкой,
; а также механизм остановки и повторного пуска машины вывода
; Русский текст в комментариях разрешён!

(deftemplate ioproxy  ; шаблон факта-посредника для обмена информацией с GUI
	(slot fact-id)        ; теоретически тут id факта для изменения
	(multislot answers)   ; возможные ответы
	(multislot messages)  ; исходящие сообщения
	(slot reaction)       ; возможные ответы пользователя
	(slot value)          ; выбор пользователя
	(slot restore)        ; забыл зачем это поле
)

; Собственно экземпляр факта ioproxy
(deffacts proxy-fact
	(ioproxy
		(fact-id 0112) ; это поле пока что не задействовано
		(value none)   ; значение пустое
		(messages)     ; мультислот messages изначально пуст
	)
)

(defrule clear-messages
	(declare (salience 90))
	?clear-msg-flg <- (clearmessage)
	?proxy <- (ioproxy)
	=>
	(modify ?proxy (messages))
	(retract ?clear-msg-flg)
	(printout t "Messages cleared ..." crlf)	
)

(defrule set-output-and-halt
	(declare (salience 99))
	?current-message <- (sendmessagehalt ?new-msg)
	?proxy <- (ioproxy (messages $?msg-list))
	=>
	(printout t "Message set : " ?new-msg " ... halting ..." crlf)
	(modify ?proxy (messages ?new-msg))
	(retract ?current-message)
	(halt)
)

(defrule append-output-and-halt
	(declare (salience 99))
	?current-message <- (appendmessagehalt ?new-msg)
	?proxy <- (ioproxy (messages $?msg-list))
	=>
	(printout t "Message appended with : " ?new-msg " ... halting ..." crlf)
	(modify ?proxy (messages $?msg-list ?new-msg))
	(retract ?current-message)
	(halt)
)

(defrule set-output-and-proceed
	(declare (salience 99))
	?current-message <- (sendmessage ?new-msg)
	?proxy <- (ioproxy (messages $?msg-list))
	=>
	(printout t "Message set : " ?new-msg crlf)
	(modify ?proxy (messages ?new-msg))
	(retract ?current-message)
)

(defrule append-output-and-proceed
	(declare (salience 99))
	?current-message <- (appendmessage ?new-msg)
	?proxy <- (ioproxy (messages $?msg-list))
	=>
	(printout t "Message appended with : " ?new-msg crlf)
	(modify ?proxy (messages $?msg-list ?new-msg))
	(retract ?current-message)
)

(deftemplate theorem
 (slot name)
 (slot coef (type FLOAT) (default 1.0))
)

(defrule combinate
	(declare (salience 90))
	?fact1 <- (theorem (name ?n1) (coef ?c1))
	?fact2 <- (theorem (name ?n2) (coef ?c2))
	=>
	(if (and (eq ?n1 ?n2) (!= ?c1 ?c2)) then
		(assert  (theorem (name ?n1) (coef (- (+ ?c1 ?c2) (* ?c1 ?c2)))))
		(retract ?fact1)
		(retract ?fact2)
(assert ( appendmessage (str-cat "
НОВЫЙ КОЭФИЦИЕНТ для " ?n1 ": (" ?c1 "+" ?c2 ")-(" ?c1 "*" ?c2 ")=" (- (+ ?c1 ?c2) (* ?c1 ?c2))
)))
)
)

;======================================================================================
(defrule rule_0
(declare (salience 20))
    (theorem (name Полнота_действительных_чисел) (coef ?c1))
    =>
    (assert( appendmessage (str-cat "Из <Полнота_действительных_чисел> доказали <Теорема_о_существовании_предела_монотонной_ограниченной_последовательности> (0.23*" (min  ?c1) "="(* 0.23 (min ?c1))")")))
    (assert (theorem (name Теорема_о_существовании_предела_монотонной_ограниченной_последовательности) (coef (* 0.23 (min ?c1)))))
)

(defrule rule_1
(declare (salience 20))
    (theorem (name Полнота_действительных_чисел) (coef ?c1))
    =>
    (assert( appendmessage (str-cat "Из <Полнота_действительных_чисел> доказали <Теорема_о_существовании_и_единственности_предела> (0.23*" (min  ?c1) "="(* 0.23 (min ?c1))")")))
    (assert (theorem (name Теорема_о_существовании_и_единственности_предела) (coef (* 0.23 (min ?c1)))))
)

(defrule rule_2
(declare (salience 20))
    (theorem (name Полнота_действительных_чисел) (coef ?c1))
    (theorem (name Предел_последовательности_Коши) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Полнота_действительных_чисел> и <Предел_последовательности_Коши> доказали <Теорема_Больцано-Вейерштрасса> (0.14*" (min  ?c1 ?c2) "="(* 0.14 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_Больцано-Вейерштрасса) (coef (* 0.14 (min ?c1 ?c2)))))
)

(defrule rule_3
(declare (salience 20))
    (theorem (name Полнота_действительных_чисел) (coef ?c1))
    (theorem (name Теорема_о_существовании_предела_монотонной_ограниченной_последовательности) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Полнота_действительных_чисел> и <Теорема_о_существовании_предела_монотонной_ограниченной_последовательности> доказали <Теорема_о_промежуточных_значениях> (0.4*" (min  ?c1 ?c2) "="(* 0.4 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_промежуточных_значениях) (coef (* 0.4 (min ?c1 ?c2)))))
)

(defrule rule_4
(declare (salience 20))
    (theorem (name Теорема_о_существовании_предела_монотонной_ограниченной_последовательности) (coef ?c1))
    (theorem (name Теорема_о_существовании_и_единственности_предела) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_существовании_предела_монотонной_ограниченной_последовательности> и <Теорема_о_существовании_и_единственности_предела> доказали <Теорема_о_предельном_переходе_в_неравенствах> (0.96*" (min  ?c1 ?c2) "="(* 0.96 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_предельном_переходе_в_неравенствах) (coef (* 0.96 (min ?c1 ?c2)))))
)

(defrule rule_5
(declare (salience 20))
    (theorem (name Непрерывность_суммы) (coef ?c1))
    (theorem (name Непрерывность_произведения) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Непрерывность_суммы> и <Непрерывность_произведения> доказали <Теорема_о_непрерывности_суммы_и_произведения_функций> (0.22*" (min  ?c1 ?c2) "="(* 0.22 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_непрерывности_суммы_и_произведения_функций) (coef (* 0.22 (min ?c1 ?c2)))))
)

(defrule rule_6
(declare (salience 20))
    (theorem (name Теорема_о_промежуточных_значениях) (coef ?c1))
    (theorem (name Теорема_о_непрерывности_суммы_и_произведения_функций) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_промежуточных_значениях> и <Теорема_о_непрерывности_суммы_и_произведения_функций> доказали <Основная_теорема_анализа> (0.25*" (min  ?c1 ?c2) "="(* 0.25 (min ?c1 ?c2))")")))
    (assert (theorem (name Основная_теорема_анализа) (coef (* 0.25 (min ?c1 ?c2)))))
)

(defrule rule_7
(declare (salience 20))
    (theorem (name Теорема_о_существовании_и_единственности_предела) (coef ?c1))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_существовании_и_единственности_предела> доказали <Свойства_пределов_сложения> (0.29*" (min  ?c1) "="(* 0.29 (min ?c1))")")))
    (assert (theorem (name Свойства_пределов_сложения) (coef (* 0.29 (min ?c1)))))
)

(defrule rule_8
(declare (salience 20))
    (theorem (name Теорема_о_существовании_и_единственности_предела) (coef ?c1))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_существовании_и_единственности_предела> доказали <Свойства_пределов_произведения> (0.74*" (min  ?c1) "="(* 0.74 (min ?c1))")")))
    (assert (theorem (name Свойства_пределов_произведения) (coef (* 0.74 (min ?c1)))))
)

(defrule rule_9
(declare (salience 20))
    (theorem (name Теорема_о_промежуточных_значениях) (coef ?c1))
    (theorem (name Основная_теорема_анализа) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_промежуточных_значениях> и <Основная_теорема_анализа> доказали <Теорема_о_среднем_значении> (0.0*" (min  ?c1 ?c2) "="(* 0.0 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_среднем_значении) (coef (* 0.0 (min ?c1 ?c2)))))
)

(defrule rule_10
(declare (salience 20))
    (theorem (name Теорема_Больцано-Вейерштрасса) (coef ?c1))
    (theorem (name Основная_теорема_анализа) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_Больцано-Вейерштрасса> и <Основная_теорема_анализа> доказали <Интегрируемость_непрерывных_функций> (0.09*" (min  ?c1 ?c2) "="(* 0.09 (min ?c1 ?c2))")")))
    (assert (theorem (name Интегрируемость_непрерывных_функций) (coef (* 0.09 (min ?c1 ?c2)))))
)

(defrule rule_11
(declare (salience 20))
    (theorem (name Аксиома_Вейерштрасса) (coef ?c1))
    (theorem (name Интегрируемость_непрерывных_функций) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Аксиома_Вейерштрасса> и <Интегрируемость_непрерывных_функций> доказали <Интегрируемость_ограниченных_функций> (0.8*" (min  ?c1 ?c2) "="(* 0.8 (min ?c1 ?c2))")")))
    (assert (theorem (name Интегрируемость_ограниченных_функций) (coef (* 0.8 (min ?c1 ?c2)))))
)

(defrule rule_12
(declare (salience 20))
    (theorem (name Теорема_о_предельном_переходе_в_неравенствах) (coef ?c1))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_предельном_переходе_в_неравенствах> доказали <Предел_производной> (0.69*" (min  ?c1) "="(* 0.69 (min ?c1))")")))
    (assert (theorem (name Предел_производной) (coef (* 0.69 (min ?c1)))))
)

(defrule rule_13
(declare (salience 20))
    (theorem (name Линейность_производной) (coef ?c1))
    (theorem (name Предел_производной) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Линейность_производной> и <Предел_производной> доказали <Дифференцируемость_суммы> (0.88*" (min  ?c1 ?c2) "="(* 0.88 (min ?c1 ?c2))")")))
    (assert (theorem (name Дифференцируемость_суммы) (coef (* 0.88 (min ?c1 ?c2)))))
)

(defrule rule_14
(declare (salience 20))
    (theorem (name Линейность_производной) (coef ?c1))
    (theorem (name Предел_производной) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Линейность_производной> и <Предел_производной> доказали <Дифференцируемость_произведения> (0.05*" (min  ?c1 ?c2) "="(* 0.05 (min ?c1 ?c2))")")))
    (assert (theorem (name Дифференцируемость_произведения) (coef (* 0.05 (min ?c1 ?c2)))))
)

(defrule rule_15
(declare (salience 20))
    (theorem (name Основная_теорема_анализа) (coef ?c1))
    (theorem (name Теорема_о_среднем_значении) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Основная_теорема_анализа> и <Теорема_о_среднем_значении> доказали <Формула_Ньютона-Лейбница> (0.92*" (min  ?c1 ?c2) "="(* 0.92 (min ?c1 ?c2))")")))
    (assert (theorem (name Формула_Ньютона-Лейбница) (coef (* 0.92 (min ?c1 ?c2)))))
)

(defrule rule_16
(declare (salience 20))
    (theorem (name Теорема_о_промежуточных_значениях) (coef ?c1))
    (theorem (name Теорема_о_непрерывности_суммы_и_произведения_функций) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_промежуточных_значениях> и <Теорема_о_непрерывности_суммы_и_произведения_функций> доказали <Теорема_о_непрерывности_обратной_функции> (0.47*" (min  ?c1 ?c2) "="(* 0.47 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_непрерывности_обратной_функции) (coef (* 0.47 (min ?c1 ?c2)))))
)

(defrule rule_17
(declare (salience 20))
    (theorem (name Теорема_о_непрерывности_суммы_и_произведения_функций) (coef ?c1))
    (theorem (name Теорема_о_среднем_значении) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_непрерывности_суммы_и_произведения_функций> и <Теорема_о_среднем_значении> доказали <Существование_и_единственность_решения_дифференциального_уравнения> (0.08*" (min  ?c1 ?c2) "="(* 0.08 (min ?c1 ?c2))")")))
    (assert (theorem (name Существование_и_единственность_решения_дифференциального_уравнения) (coef (* 0.08 (min ?c1 ?c2)))))
)

(defrule rule_18
(declare (salience 20))
    (theorem (name Теорема_о_существовании_и_единственности_предела) (coef ?c1))
    (theorem (name Теорема_о_предельном_переходе_в_неравенствах) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_существовании_и_единственности_предела> и <Теорема_о_предельном_переходе_в_неравенствах> доказали <Теорема_об_единственности_предела> (0.99*" (min  ?c1 ?c2) "="(* 0.99 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_об_единственности_предела) (coef (* 0.99 (min ?c1 ?c2)))))
)

(defrule rule_19
(declare (salience 20))
    (theorem (name Основная_теорема_анализа) (coef ?c1))
    (theorem (name Формула_Ньютона-Лейбница) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Основная_теорема_анализа> и <Формула_Ньютона-Лейбница> доказали <Теорема_о_замене_переменной_в_интеграле> (0.9*" (min  ?c1 ?c2) "="(* 0.9 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_замене_переменной_в_интеграле) (coef (* 0.9 (min ?c1 ?c2)))))
)

(defrule rule_20
(declare (salience 20))
    (theorem (name Теорема_о_непрерывности_суммы_и_произведения_функций) (coef ?c1))
    (theorem (name Интегрируемость_непрерывных_функций) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_непрерывности_суммы_и_произведения_функций> и <Интегрируемость_непрерывных_функций> доказали <Свойства_интегралов> (0.17*" (min  ?c1 ?c2) "="(* 0.17 (min ?c1 ?c2))")")))
    (assert (theorem (name Свойства_интегралов) (coef (* 0.17 (min ?c1 ?c2)))))
)

(defrule rule_21
(declare (salience 20))
    (theorem (name Теорема_о_непрерывности_суммы_и_произведения_функций) (coef ?c1))
    (theorem (name Предел_производной) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_непрерывности_суммы_и_произведения_функций> и <Предел_производной> доказали <Свойства_производных> (0.74*" (min  ?c1 ?c2) "="(* 0.74 (min ?c1 ?c2))")")))
    (assert (theorem (name Свойства_производных) (coef (* 0.74 (min ?c1 ?c2)))))
)

(defrule rule_22
(declare (salience 20))
    (theorem (name Теорема_о_среднем_значении) (coef ?c1))
    (theorem (name Дифференцируемость_суммы) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_среднем_значении> и <Дифференцируемость_суммы> доказали <Ряд_Тейлора> (0.39*" (min  ?c1 ?c2) "="(* 0.39 (min ?c1 ?c2))")")))
    (assert (theorem (name Ряд_Тейлора) (coef (* 0.39 (min ?c1 ?c2)))))
)

(defrule rule_23
(declare (salience 20))
    (theorem (name Интегрируемость_непрерывных_функций) (coef ?c1))
    (theorem (name Предел_производной) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Интегрируемость_непрерывных_функций> и <Предел_производной> доказали <Интегрируемость_непрерывно_дифференцируемых_функций> (0.5*" (min  ?c1 ?c2) "="(* 0.5 (min ?c1 ?c2))")")))
    (assert (theorem (name Интегрируемость_непрерывно_дифференцируемых_функций) (coef (* 0.5 (min ?c1 ?c2)))))
)

(defrule rule_24
(declare (salience 20))
    (theorem (name Интегрируемость_непрерывных_функций) (coef ?c1))
    (theorem (name Интегрируемость_ограниченных_функций) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Интегрируемость_непрерывных_функций> и <Интегрируемость_ограниченных_функций> доказали <Сходимость_интегралов_Римана> (0.98*" (min  ?c1 ?c2) "="(* 0.98 (min ?c1 ?c2))")")))
    (assert (theorem (name Сходимость_интегралов_Римана) (coef (* 0.98 (min ?c1 ?c2)))))
)

(defrule rule_25
(declare (salience 20))
    (theorem (name Теорема_о_предельном_переходе_в_неравенствах) (coef ?c1))
    (theorem (name Ряд_Тейлора) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_предельном_переходе_в_неравенствах> и <Ряд_Тейлора> доказали <Признак_сходимости_ряда> (0.04*" (min  ?c1 ?c2) "="(* 0.04 (min ?c1 ?c2))")")))
    (assert (theorem (name Признак_сходимости_ряда) (coef (* 0.04 (min ?c1 ?c2)))))
)

(defrule rule_26
(declare (salience 20))
    (theorem (name Признак_сходимости_ряда) (coef ?c1))
    =>
    (assert( appendmessage (str-cat "Из <Признак_сходимости_ряда> доказали <Признак_Даламбера> (0.22*" (min  ?c1) "="(* 0.22 (min ?c1))")")))
    (assert (theorem (name Признак_Даламбера) (coef (* 0.22 (min ?c1)))))
)

(defrule rule_27
(declare (salience 20))
    (theorem (name Признак_сходимости_ряда) (coef ?c1))
    =>
    (assert( appendmessage (str-cat "Из <Признак_сходимости_ряда> доказали <Признак_сравнения_для_рядов> (0.35*" (min  ?c1) "="(* 0.35 (min ?c1))")")))
    (assert (theorem (name Признак_сравнения_для_рядов) (coef (* 0.35 (min ?c1)))))
)

(defrule rule_28
(declare (salience 20))
    (theorem (name Теорема_Больцано-Вейерштрасса) (coef ?c1))
    (theorem (name Теорема_о_предельном_переходе_в_неравенствах) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_Больцано-Вейерштрасса> и <Теорема_о_предельном_переходе_в_неравенствах> доказали <Теорема_о_лемме_Фату> (0.61*" (min  ?c1 ?c2) "="(* 0.61 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_лемме_Фату) (coef (* 0.61 (min ?c1 ?c2)))))
)

(defrule rule_29
(declare (salience 20))
    (theorem (name Теорема_о_непрерывности_обратной_функции) (coef ?c1))
    (theorem (name Теорема_о_промежуточных_значениях) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_непрерывности_обратной_функции> и <Теорема_о_промежуточных_значениях> доказали <Теорема_о_равномерной_непрерывности> (0.84*" (min  ?c1 ?c2) "="(* 0.84 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_равномерной_непрерывности) (coef (* 0.84 (min ?c1 ?c2)))))
)

(defrule rule_30
(declare (salience 20))
    (theorem (name Свойства_пределов_сложения) (coef ?c1))
    (theorem (name Теорема_об_единственности_предела) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Свойства_пределов_сложения> и <Теорема_об_единственности_предела> доказали <Теорема_о_непрерывности_предела> (0.36*" (min  ?c1 ?c2) "="(* 0.36 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_непрерывности_предела) (coef (* 0.36 (min ?c1 ?c2)))))
)

(defrule rule_31
(declare (salience 20))
    (theorem (name Теорема_Больцано-Вейерштрасса) (coef ?c1))
    (theorem (name Свойства_пределов_сложения) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_Больцано-Вейерштрасса> и <Свойства_пределов_сложения> доказали <Теорема_о_точечной_сходимости_последовательности_функций> (0.64*" (min  ?c1 ?c2) "="(* 0.64 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_точечной_сходимости_последовательности_функций) (coef (* 0.64 (min ?c1 ?c2)))))
)

(defrule rule_32
(declare (salience 20))
    (theorem (name Интегрируемость_непрерывных_функций) (coef ?c1))
    (theorem (name Теорема_о_точечной_сходимости_последовательности_функций) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Интегрируемость_непрерывных_функций> и <Теорема_о_точечной_сходимости_последовательности_функций> доказали <Теорема_о_предельном_переходе_в_интегралах> (0.62*" (min  ?c1 ?c2) "="(* 0.62 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_предельном_переходе_в_интегралах) (coef (* 0.62 (min ?c1 ?c2)))))
)

(defrule rule_33
(declare (salience 20))
    (theorem (name Ряд_Тейлора) (coef ?c1))
    (theorem (name Теорема_о_непрерывности_предела) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Ряд_Тейлора> и <Теорема_о_непрерывности_предела> доказали <Теорема_о_пределе_ряда_функций> (0.7*" (min  ?c1 ?c2) "="(* 0.7 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_пределе_ряда_функций) (coef (* 0.7 (min ?c1 ?c2)))))
)

(defrule rule_34
(declare (salience 20))
    (theorem (name Ряд_Тейлора) (coef ?c1))
    (theorem (name Теорема_о_пределе_ряда_функций) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Ряд_Тейлора> и <Теорема_о_пределе_ряда_функций> доказали <Свойства_рядов_Тейлора> (0.58*" (min  ?c1 ?c2) "="(* 0.58 (min ?c1 ?c2))")")))
    (assert (theorem (name Свойства_рядов_Тейлора) (coef (* 0.58 (min ?c1 ?c2)))))
)

(defrule rule_35
(declare (salience 20))
    (theorem (name Интегрируемость_непрерывных_функций) (coef ?c1))
    (theorem (name Сходимость_интегралов_Римана) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Интегрируемость_непрерывных_функций> и <Сходимость_интегралов_Римана> доказали <Признак_сходимости_интегралов> (0.66*" (min  ?c1 ?c2) "="(* 0.66 (min ?c1 ?c2))")")))
    (assert (theorem (name Признак_сходимости_интегралов) (coef (* 0.66 (min ?c1 ?c2)))))
)

(defrule rule_36
(declare (salience 20))
    (theorem (name Признак_сходимости_интегралов) (coef ?c1))
    =>
    (assert( appendmessage (str-cat "Из <Признак_сходимости_интегралов> доказали <Признак_сходимости_Абеля> (0.02*" (min  ?c1) "="(* 0.02 (min ?c1))")")))
    (assert (theorem (name Признак_сходимости_Абеля) (coef (* 0.02 (min ?c1)))))
)

(defrule rule_37
(declare (salience 20))
    (theorem (name Теорема_о_точечной_сходимости_последовательности_функций) (coef ?c1))
    (theorem (name Теорема_о_предельном_переходе_в_интегралах) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_точечной_сходимости_последовательности_функций> и <Теорема_о_предельном_переходе_в_интегралах> доказали <Теорема_Вейерштрасса_о_сходимости_ряда_функций> (0.77*" (min  ?c1 ?c2) "="(* 0.77 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_Вейерштрасса_о_сходимости_ряда_функций) (coef (* 0.77 (min ?c1 ?c2)))))
)

(defrule rule_38
(declare (salience 20))
    (theorem (name Интегрируемость_непрерывных_функций) (coef ?c1))
    (theorem (name Свойства_производных) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Интегрируемость_непрерывных_функций> и <Свойства_производных> доказали <Теорема_о_дифференцировании_под_знаком_интеграла> (0.02*" (min  ?c1 ?c2) "="(* 0.02 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_дифференцировании_под_знаком_интеграла) (coef (* 0.02 (min ?c1 ?c2)))))
)

(defrule rule_39
(declare (salience 20))
    (theorem (name Интегрируемость_непрерывных_функций) (coef ?c1))
    (theorem (name Теорема_о_предельном_переходе_в_интегралах) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Интегрируемость_непрерывных_функций> и <Теорема_о_предельном_переходе_в_интегралах> доказали <Теорема_о_непрерывности_интеграла_по_параметру> (0.69*" (min  ?c1 ?c2) "="(* 0.69 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_непрерывности_интеграла_по_параметру) (coef (* 0.69 (min ?c1 ?c2)))))
)

(defrule rule_40
(declare (salience 20))
    (theorem (name Теорема_о_замене_переменной_в_интеграле) (coef ?c1))
    (theorem (name Свойства_интегралов) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_замене_переменной_в_интеграле> и <Свойства_интегралов> доказали <Теорема_Стокса> (0.93*" (min  ?c1 ?c2) "="(* 0.93 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_Стокса) (coef (* 0.93 (min ?c1 ?c2)))))
)

(defrule rule_41
(declare (salience 20))
    (theorem (name Основная_теорема_анализа) (coef ?c1))
    (theorem (name Теорема_Стокса) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Основная_теорема_анализа> и <Теорема_Стокса> доказали <Теорема_Гаусса-Остроградского> (0.51*" (min  ?c1 ?c2) "="(* 0.51 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_Гаусса-Остроградского) (coef (* 0.51 (min ?c1 ?c2)))))
)

(defrule rule_42
(declare (salience 20))
    (theorem (name Интегрируемость_непрерывных_функций) (coef ?c1))
    (theorem (name Свойства_интегралов) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Интегрируемость_непрерывных_функций> и <Свойства_интегралов> доказали <Теорема_о_характеристическом_свойстве_интеграла> (0.07*" (min  ?c1 ?c2) "="(* 0.07 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_характеристическом_свойстве_интеграла) (coef (* 0.07 (min ?c1 ?c2)))))
)

(defrule rule_43
(declare (salience 20))
    (theorem (name Теорема_о_равномерной_непрерывности) (coef ?c1))
    (theorem (name Теорема_Вейерштрасса_о_сходимости_ряда_функций) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_равномерной_непрерывности> и <Теорема_Вейерштрасса_о_сходимости_ряда_функций> доказали <Признак_Вейерштрасса> (0.29*" (min  ?c1 ?c2) "="(* 0.29 (min ?c1 ?c2))")")))
    (assert (theorem (name Признак_Вейерштрасса) (coef (* 0.29 (min ?c1 ?c2)))))
)

(defrule rule_44
(declare (salience 20))
    (theorem (name Теорема_Больцано-Вейерштрасса) (coef ?c1))
    (theorem (name Теорема_о_предельном_переходе_в_интегралах) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_Больцано-Вейерштрасса> и <Теорема_о_предельном_переходе_в_интегралах> доказали <Интеграл_Лебега> (0.46*" (min  ?c1 ?c2) "="(* 0.46 (min ?c1 ?c2))")")))
    (assert (theorem (name Интеграл_Лебега) (coef (* 0.46 (min ?c1 ?c2)))))
)

(defrule rule_45
(declare (salience 20))
    (theorem (name Интегрируемость_непрерывных_функций) (coef ?c1))
    (theorem (name Теорема_о_дифференцировании_под_знаком_интеграла) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Интегрируемость_непрерывных_функций> и <Теорема_о_дифференцировании_под_знаком_интеграла> доказали <Теорема_о_смене_порядка_интегрирования> (0.56*" (min  ?c1 ?c2) "="(* 0.56 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_смене_порядка_интегрирования) (coef (* 0.56 (min ?c1 ?c2)))))
)

(defrule rule_46
(declare (salience 20))
    (theorem (name Признак_сходимости_интегралов) (coef ?c1))
    (theorem (name Теорема_о_характеристическом_свойстве_интеграла) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Признак_сходимости_интегралов> и <Теорема_о_характеристическом_свойстве_интеграла> доказали <Признак_Коши_сходимости_интегралов> (0.38*" (min  ?c1 ?c2) "="(* 0.38 (min ?c1 ?c2))")")))
    (assert (theorem (name Признак_Коши_сходимости_интегралов) (coef (* 0.38 (min ?c1 ?c2)))))
)

(defrule rule_47
(declare (salience 20))
    (theorem (name Интеграл_Лебега) (coef ?c1))
    (theorem (name Теорема_Вейерштрасса_о_сходимости_ряда_функций) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Интеграл_Лебега> и <Теорема_Вейерштрасса_о_сходимости_ряда_функций> доказали <Теорема_о_компактности_в_Lp-пространствах> (0.08*" (min  ?c1 ?c2) "="(* 0.08 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_компактности_в_Lp-пространствах) (coef (* 0.08 (min ?c1 ?c2)))))
)

(defrule rule_48
(declare (salience 20))
    (theorem (name Признак_сходимости_ряда) (coef ?c1))
    (theorem (name Признак_сходимости_Абеля) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Признак_сходимости_ряда> и <Признак_сходимости_Абеля> доказали <Признак_абсолютной_сходимости> (0.17*" (min  ?c1 ?c2) "="(* 0.17 (min ?c1 ?c2))")")))
    (assert (theorem (name Признак_абсолютной_сходимости) (coef (* 0.17 (min ?c1 ?c2)))))
)

(defrule rule_49
(declare (salience 20))
    (theorem (name Теорема_о_равномерной_непрерывности) (coef ?c1))
    (theorem (name Теорема_о_точечной_сходимости_последовательности_функций) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_равномерной_непрерывности> и <Теорема_о_точечной_сходимости_последовательности_функций> доказали <Теорема_о_последовательности_непрерывных_функций> (0.32*" (min  ?c1 ?c2) "="(* 0.32 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_последовательности_непрерывных_функций) (coef (* 0.32 (min ?c1 ?c2)))))
)

(defrule rule_50
(declare (salience 20))
    (theorem (name Теорема_о_непрерывности_предела) (coef ?c1))
    (theorem (name Теорема_о_последовательности_непрерывных_функций) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_непрерывности_предела> и <Теорема_о_последовательности_непрерывных_функций> доказали <Теорема_о_равномерной_сходимости_последовательности_функций> (0.24*" (min  ?c1 ?c2) "="(* 0.24 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_равномерной_сходимости_последовательности_функций) (coef (* 0.24 (min ?c1 ?c2)))))
)

(defrule rule_51
(declare (salience 20))
    (theorem (name Свойства_производных) (coef ?c1))
    (theorem (name Интегрируемость_непрерывно_дифференцируемых_функций) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Свойства_производных> и <Интегрируемость_непрерывно_дифференцируемых_функций> доказали <Свойства_функций_класса_C1> (0.97*" (min  ?c1 ?c2) "="(* 0.97 (min ?c1 ?c2))")")))
    (assert (theorem (name Свойства_функций_класса_C1) (coef (* 0.97 (min ?c1 ?c2)))))
)

(defrule rule_52
(declare (salience 20))
    (theorem (name Дифференцируемость_суммы) (coef ?c1))
    (theorem (name Теорема_о_дифференцировании_под_знаком_интеграла) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Дифференцируемость_суммы> и <Теорема_о_дифференцировании_под_знаком_интеграла> доказали <Дифференцирование_под_знаком_суммы> (0.53*" (min  ?c1 ?c2) "="(* 0.53 (min ?c1 ?c2))")")))
    (assert (theorem (name Дифференцирование_под_знаком_суммы) (coef (* 0.53 (min ?c1 ?c2)))))
)

(defrule rule_53
(declare (salience 20))
    (theorem (name Теорема_о_замене_переменной_в_интеграле) (coef ?c1))
    (theorem (name Теорема_о_смене_порядка_интегрирования) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_замене_переменной_в_интеграле> и <Теорема_о_смене_порядка_интегрирования> доказали <Теорема_о_замене_переменной_в_кратном_интеграле> (0.71*" (min  ?c1 ?c2) "="(* 0.71 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_замене_переменной_в_кратном_интеграле) (coef (* 0.71 (min ?c1 ?c2)))))
)

(defrule rule_54
(declare (salience 20))
    (theorem (name Теорема_о_характеристическом_свойстве_интеграла) (coef ?c1))
    (theorem (name Интеграл_Лебега) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_характеристическом_свойстве_интеграла> и <Интеграл_Лебега> доказали <Теорема_о_непрерывности_меры> (0.94*" (min  ?c1 ?c2) "="(* 0.94 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_непрерывности_меры) (coef (* 0.94 (min ?c1 ?c2)))))
)

(defrule rule_55
(declare (salience 20))
    (theorem (name Свойства_пределов_сложения) (coef ?c1))
    (theorem (name Теорема_об_единственности_предела) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Свойства_пределов_сложения> и <Теорема_об_единственности_предела> доказали <Лемма_о_распределении_предела> (0.64*" (min  ?c1 ?c2) "="(* 0.64 (min ?c1 ?c2))")")))
    (assert (theorem (name Лемма_о_распределении_предела) (coef (* 0.64 (min ?c1 ?c2)))))
)

(defrule rule_56
(declare (salience 20))
    (theorem (name Теорема_о_компактности_в_Lp-пространствах) (coef ?c1))
    (theorem (name Теорема_о_равномерной_непрерывности) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_компактности_в_Lp-пространствах> и <Теорема_о_равномерной_непрерывности> доказали <Теорема_о_линейной_непрерывности_оператора> (0.21*" (min  ?c1 ?c2) "="(* 0.21 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_линейной_непрерывности_оператора) (coef (* 0.21 (min ?c1 ?c2)))))
)

(defrule rule_57
(declare (salience 20))
    (theorem (name Теорема_о_замене_переменной_в_интеграле) (coef ?c1))
    (theorem (name Свойства_функций_класса_C1) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_замене_переменной_в_интеграле> и <Свойства_функций_класса_C1> доказали <Теорема_о_преобразовании_Фурье> (0.48*" (min  ?c1 ?c2) "="(* 0.48 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_преобразовании_Фурье) (coef (* 0.48 (min ?c1 ?c2)))))
)

(defrule rule_58
(declare (salience 20))
    (theorem (name Теорема_о_преобразовании_Фурье) (coef ?c1))
    (theorem (name Теорема_о_равномерной_непрерывности) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_преобразовании_Фурье> и <Теорема_о_равномерной_непрерывности> доказали <Свойства_преобразования_Фурье> (0.38*" (min  ?c1 ?c2) "="(* 0.38 (min ?c1 ?c2))")")))
    (assert (theorem (name Свойства_преобразования_Фурье) (coef (* 0.38 (min ?c1 ?c2)))))
)

(defrule rule_59
(declare (salience 20))
    (theorem (name Интеграл_Лебега) (coef ?c1))
    (theorem (name Теорема_о_замене_переменной_в_кратном_интеграле) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Интеграл_Лебега> и <Теорема_о_замене_переменной_в_кратном_интеграле> доказали <Теорема_о_замене_переменной_для_интегралов_Лебега> (0.84*" (min  ?c1 ?c2) "="(* 0.84 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_замене_переменной_для_интегралов_Лебега) (coef (* 0.84 (min ?c1 ?c2)))))
)

(defrule rule_60
(declare (salience 20))
    (theorem (name Свойства_производных) (coef ?c1))
    (theorem (name Теорема_Стокса) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Свойства_производных> и <Теорема_Стокса> доказали <Свойства_градиента> (0.57*" (min  ?c1 ?c2) "="(* 0.57 (min ?c1 ?c2))")")))
    (assert (theorem (name Свойства_градиента) (coef (* 0.57 (min ?c1 ?c2)))))
)

(defrule rule_61
(declare (salience 20))
    (theorem (name Теорема_Гаусса-Остроградского) (coef ?c1))
    (theorem (name Теорема_о_характеристическом_свойстве_интеграла) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_Гаусса-Остроградского> и <Теорема_о_характеристическом_свойстве_интеграла> доказали <Свойства_дивергенции> (0.69*" (min  ?c1 ?c2) "="(* 0.69 (min ?c1 ?c2))")")))
    (assert (theorem (name Свойства_дивергенции) (coef (* 0.69 (min ?c1 ?c2)))))
)

(defrule rule_62
(declare (salience 20))
    (theorem (name Интеграл_Лебега) (coef ?c1))
    (theorem (name Теорема_о_лемме_Фату) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Интеграл_Лебега> и <Теорема_о_лемме_Фату> доказали <Лемма_Фату_для_интегралов_Лебега> (0.68*" (min  ?c1 ?c2) "="(* 0.68 (min ?c1 ?c2))")")))
    (assert (theorem (name Лемма_Фату_для_интегралов_Лебега) (coef (* 0.68 (min ?c1 ?c2)))))
)

(defrule rule_63
(declare (salience 20))
    (theorem (name Теорема_о_предельном_переходе_в_неравенствах) (coef ?c1))
    (theorem (name Признак_сравнения_для_рядов) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_предельном_переходе_в_неравенствах> и <Признак_сравнения_для_рядов> доказали <Теорема_о_выпуклых_функциях> (0.49*" (min  ?c1 ?c2) "="(* 0.49 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_выпуклых_функциях) (coef (* 0.49 (min ?c1 ?c2)))))
)

(defrule rule_64
(declare (salience 20))
    (theorem (name Теорема_о_выпуклых_функциях) (coef ?c1))
    (theorem (name Основная_теорема_анализа) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_выпуклых_функциях> и <Основная_теорема_анализа> доказали <Теорема_о_неравенстве_Йенсена> (0.0*" (min  ?c1 ?c2) "="(* 0.0 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_неравенстве_Йенсена) (coef (* 0.0 (min ?c1 ?c2)))))
)

(defrule rule_65
(declare (salience 20))
    (theorem (name Признак_Коши_сходимости_интегралов) (coef ?c1))
    (theorem (name Теорема_о_смене_порядка_интегрирования) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Признак_Коши_сходимости_интегралов> и <Теорема_о_смене_порядка_интегрирования> доказали <Теорема_о_независимости_порядка_интегрирования_в_условных_интегралах> (0.94*" (min  ?c1 ?c2) "="(* 0.94 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_независимости_порядка_интегрирования_в_условных_интегралах) (coef (* 0.94 (min ?c1 ?c2)))))
)

(defrule rule_66
(declare (salience 20))
    (theorem (name Свойства_функций_класса_C1) (coef ?c1))
    (theorem (name Основная_теорема_анализа) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Свойства_функций_класса_C1> и <Основная_теорема_анализа> доказали <Теорема_о_спрямляемых_кривых> (0.58*" (min  ?c1 ?c2) "="(* 0.58 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_спрямляемых_кривых) (coef (* 0.58 (min ?c1 ?c2)))))
)

(defrule rule_67
(declare (salience 20))
    (theorem (name Интеграл_Лебега) (coef ?c1))
    (theorem (name Теорема_о_компактности_в_Lp-пространствах) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Интеграл_Лебега> и <Теорема_о_компактности_в_Lp-пространствах> доказали <Неравенство_Гёльдера> (0.77*" (min  ?c1 ?c2) "="(* 0.77 (min ?c1 ?c2))")")))
    (assert (theorem (name Неравенство_Гёльдера) (coef (* 0.77 (min ?c1 ?c2)))))
)

(defrule rule_68
(declare (salience 20))
    (theorem (name Теорема_о_компактности_в_Lp-пространствах) (coef ?c1))
    (theorem (name Неравенство_Гёльдера) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_компактности_в_Lp-пространствах> и <Неравенство_Гёльдера> доказали <Неравенство_Минковского> (0.13*" (min  ?c1 ?c2) "="(* 0.13 (min ?c1 ?c2))")")))
    (assert (theorem (name Неравенство_Минковского) (coef (* 0.13 (min ?c1 ?c2)))))
)

(defrule rule_69
(declare (salience 20))
    (theorem (name Признак_Вейерштрасса) (coef ?c1))
    (theorem (name Теорема_о_компактности_в_Lp-пространствах) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Признак_Вейерштрасса> и <Теорема_о_компактности_в_Lp-пространствах> доказали <Принцип_локальной_компактности> (0.42*" (min  ?c1 ?c2) "="(* 0.42 (min ?c1 ?c2))")")))
    (assert (theorem (name Принцип_локальной_компактности) (coef (* 0.42 (min ?c1 ?c2)))))
)

(defrule rule_70
(declare (salience 20))
    (theorem (name Интеграл_Лебега) (coef ?c1))
    (theorem (name Лемма_Фату_для_интегралов_Лебега) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Интеграл_Лебега> и <Лемма_Фату_для_интегралов_Лебега> доказали <Теорема_о_пределе_интегралов_Лебега> (0.24*" (min  ?c1 ?c2) "="(* 0.24 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_пределе_интегралов_Лебега) (coef (* 0.24 (min ?c1 ?c2)))))
)

(defrule rule_71
(declare (salience 20))
    (theorem (name Лемма_Фату_для_интегралов_Лебега) (coef ?c1))
    (theorem (name Теорема_о_пределе_интегралов_Лебега) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Лемма_Фату_для_интегралов_Лебега> и <Теорема_о_пределе_интегралов_Лебега> доказали <Лемма_о_сходимости_Фату> (0.08*" (min  ?c1 ?c2) "="(* 0.08 (min ?c1 ?c2))")")))
    (assert (theorem (name Лемма_о_сходимости_Фату) (coef (* 0.08 (min ?c1 ?c2)))))
)

(defrule rule_72
(declare (salience 20))
    (theorem (name Неравенство_Гёльдера) (coef ?c1))
    (theorem (name Теорема_о_пределе_интегралов_Лебега) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Неравенство_Гёльдера> и <Теорема_о_пределе_интегралов_Лебега> доказали <Неравенство_Чебышёва_для_интегралов> (0.6*" (min  ?c1 ?c2) "="(* 0.6 (min ?c1 ?c2))")")))
    (assert (theorem (name Неравенство_Чебышёва_для_интегралов) (coef (* 0.6 (min ?c1 ?c2)))))
)

(defrule rule_73
(declare (salience 20))
    (theorem (name Признак_сходимости_ряда) (coef ?c1))
    (theorem (name Признак_сходимости_Абеля) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Признак_сходимости_ряда> и <Признак_сходимости_Абеля> доказали <Признак_Абеля_для_рядов> (0.82*" (min  ?c1 ?c2) "="(* 0.82 (min ?c1 ?c2))")")))
    (assert (theorem (name Признак_Абеля_для_рядов) (coef (* 0.82 (min ?c1 ?c2)))))
)

(defrule rule_74
(declare (salience 20))
    (theorem (name Теорема_о_непрерывности_меры) (coef ?c1))
    (theorem (name Теорема_о_замене_переменной_для_интегралов_Лебега) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_непрерывности_меры> и <Теорема_о_замене_переменной_для_интегралов_Лебега> доказали <Теорема_о_линейности_интеграла_Лебега> (0.36*" (min  ?c1 ?c2) "="(* 0.36 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_линейности_интеграла_Лебега) (coef (* 0.36 (min ?c1 ?c2)))))
)

(defrule rule_75
(declare (salience 20))
    (theorem (name Признак_абсолютной_сходимости) (coef ?c1))
    (theorem (name Теорема_о_последовательности_непрерывных_функций) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Признак_абсолютной_сходимости> и <Теорема_о_последовательности_непрерывных_функций> доказали <Признак_Римана_для_абсолютной_сходимости> (0.86*" (min  ?c1 ?c2) "="(* 0.86 (min ?c1 ?c2))")")))
    (assert (theorem (name Признак_Римана_для_абсолютной_сходимости) (coef (* 0.86 (min ?c1 ?c2)))))
)

(defrule rule_76
(declare (salience 20))
    (theorem (name Теорема_о_компактности_в_Lp-пространствах) (coef ?c1))
    (theorem (name Неравенство_Минковского) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_компактности_в_Lp-пространствах> и <Неравенство_Минковского> доказали <Лемма_о_слабой_сходимости> (0.09*" (min  ?c1 ?c2) "="(* 0.09 (min ?c1 ?c2))")")))
    (assert (theorem (name Лемма_о_слабой_сходимости) (coef (* 0.09 (min ?c1 ?c2)))))
)

(defrule rule_77
(declare (salience 20))
    (theorem (name Теорема_о_непрерывности_меры) (coef ?c1))
    (theorem (name Лемма_о_слабой_сходимости) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_непрерывности_меры> и <Лемма_о_слабой_сходимости> доказали <Теорема_о_слабой_сходимости_в_Lp-пространствах> (0.28*" (min  ?c1 ?c2) "="(* 0.28 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_слабой_сходимости_в_Lp-пространствах) (coef (* 0.28 (min ?c1 ?c2)))))
)

(defrule rule_78
(declare (salience 20))
    (theorem (name Неравенство_Гёльдера) (coef ?c1))
    (theorem (name Неравенство_Минковского) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Неравенство_Гёльдера> и <Неравенство_Минковского> доказали <Теорема_о_неравенстве_Хёльдера> (0.45*" (min  ?c1 ?c2) "="(* 0.45 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_неравенстве_Хёльдера) (coef (* 0.45 (min ?c1 ?c2)))))
)

(defrule rule_79
(declare (salience 20))
    (theorem (name Неравенство_Минковского) (coef ?c1))
    (theorem (name Теорема_о_слабой_сходимости_в_Lp-пространствах) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Неравенство_Минковского> и <Теорема_о_слабой_сходимости_в_Lp-пространствах> доказали <Теорема_о_свойствах_пространства_L2> (0.11*" (min  ?c1 ?c2) "="(* 0.11 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_свойствах_пространства_L2) (coef (* 0.11 (min ?c1 ?c2)))))
)

(defrule rule_80
(declare (salience 20))
    (theorem (name Теорема_о_слабой_сходимости_в_Lp-пространствах) (coef ?c1))
    (theorem (name Теорема_о_неравенстве_Хёльдера) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_слабой_сходимости_в_Lp-пространствах> и <Теорема_о_неравенстве_Хёльдера> доказали <Теорема_о_компактности_множества_в_Lp-пространствах> (0.06*" (min  ?c1 ?c2) "="(* 0.06 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_компактности_множества_в_Lp-пространствах) (coef (* 0.06 (min ?c1 ?c2)))))
)

(defrule rule_81
(declare (salience 20))
    (theorem (name Теорема_о_компактности_множества_в_Lp-пространствах) (coef ?c1))
    (theorem (name Теорема_о_свойствах_пространства_L2) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_компактности_множества_в_Lp-пространствах> и <Теорема_о_свойствах_пространства_L2> доказали <Теорема_о_неравенстве_треугольника_в_Lp-пространствах> (0.14*" (min  ?c1 ?c2) "="(* 0.14 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_неравенстве_треугольника_в_Lp-пространствах) (coef (* 0.14 (min ?c1 ?c2)))))
)

(defrule rule_82
(declare (salience 20))
    (theorem (name Теорема_о_неравенстве_Йенсена) (coef ?c1))
    (theorem (name Теорема_о_свойствах_пространства_L2) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_неравенстве_Йенсена> и <Теорема_о_свойствах_пространства_L2> доказали <Неравенство_Йенсена_в_пространстве_Lp> (0.76*" (min  ?c1 ?c2) "="(* 0.76 (min ?c1 ?c2))")")))
    (assert (theorem (name Неравенство_Йенсена_в_пространстве_Lp) (coef (* 0.76 (min ?c1 ?c2)))))
)

(defrule rule_83
(declare (salience 20))
    (theorem (name Теорема_о_линейной_непрерывности_оператора) (coef ?c1))
    (theorem (name Теорема_о_свойствах_пространства_L2) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_линейной_непрерывности_оператора> и <Теорема_о_свойствах_пространства_L2> доказали <Теорема_о_равномерной_ограниченности_операторов> (0.68*" (min  ?c1 ?c2) "="(* 0.68 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_равномерной_ограниченности_операторов) (coef (* 0.68 (min ?c1 ?c2)))))
)

(defrule rule_84
(declare (salience 20))
    (theorem (name Теорема_о_последовательности_непрерывных_функций) (coef ?c1))
    (theorem (name Теорема_о_компактности_множества_в_Lp-пространствах) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_последовательности_непрерывных_функций> и <Теорема_о_компактности_множества_в_Lp-пространствах> доказали <Теорема_о_непрерывности_сужения> (0.07*" (min  ?c1 ?c2) "="(* 0.07 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_непрерывности_сужения) (coef (* 0.07 (min ?c1 ?c2)))))
)

(defrule rule_85
(declare (salience 20))
    (theorem (name Интегрируемость_непрерывно_дифференцируемых_функций) (coef ?c1))
    (theorem (name Теорема_о_характеристическом_свойстве_интеграла) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Интегрируемость_непрерывно_дифференцируемых_функций> и <Теорема_о_характеристическом_свойстве_интеграла> доказали <Лемма_об_интегрируемых_функциях> (0.34*" (min  ?c1 ?c2) "="(* 0.34 (min ?c1 ?c2))")")))
    (assert (theorem (name Лемма_об_интегрируемых_функциях) (coef (* 0.34 (min ?c1 ?c2)))))
)

(defrule rule_86
(declare (salience 20))
    (theorem (name Дифференцируемость_суммы) (coef ?c1))
    (theorem (name Теорема_о_линейной_непрерывности_оператора) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Дифференцируемость_суммы> и <Теорема_о_линейной_непрерывности_оператора> доказали <Теорема_о_разложении_функций> (0.84*" (min  ?c1 ?c2) "="(* 0.84 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_разложении_функций) (coef (* 0.84 (min ?c1 ?c2)))))
)

(defrule rule_87
(declare (salience 20))
    (theorem (name Теорема_о_последовательности_непрерывных_функций) (coef ?c1))
    (theorem (name Теорема_о_выпуклых_функциях) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_последовательности_непрерывных_функций> и <Теорема_о_выпуклых_функциях> доказали <Теорема_о_равномерной_сходимости_функций> (0.4*" (min  ?c1 ?c2) "="(* 0.4 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_равномерной_сходимости_функций) (coef (* 0.4 (min ?c1 ?c2)))))
)

(defrule rule_88
(declare (salience 20))
    (theorem (name Основная_теорема_анализа) (coef ?c1))
    (theorem (name Теорема_о_равномерной_ограниченности_операторов) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Основная_теорема_анализа> и <Теорема_о_равномерной_ограниченности_операторов> доказали <Принцип_наименьшего_действия> (0.25*" (min  ?c1 ?c2) "="(* 0.25 (min ?c1 ?c2))")")))
    (assert (theorem (name Принцип_наименьшего_действия) (coef (* 0.25 (min ?c1 ?c2)))))
)

(defrule rule_89
(declare (salience 20))
    (theorem (name Интегрируемость_непрерывных_функций) (coef ?c1))
    (theorem (name Теорема_о_непрерывности_сужения) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Интегрируемость_непрерывных_функций> и <Теорема_о_непрерывности_сужения> доказали <Теорема_о_равномерной_ограниченности_интегралов> (0.4*" (min  ?c1 ?c2) "="(* 0.4 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_равномерной_ограниченности_интегралов) (coef (* 0.4 (min ?c1 ?c2)))))
)

(defrule rule_90
(declare (salience 20))
    (theorem (name Предел_производной) (coef ?c1))
    (theorem (name Интегрируемость_непрерывно_дифференцируемых_функций) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Предел_производной> и <Интегрируемость_непрерывно_дифференцируемых_функций> доказали <Теорема_о_непрерывности_производной> (0.69*" (min  ?c1 ?c2) "="(* 0.69 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_непрерывности_производной) (coef (* 0.69 (min ?c1 ?c2)))))
)

(defrule rule_91
(declare (salience 20))
    (theorem (name Теорема_о_компактности_в_Lp-пространствах) (coef ?c1))
    (theorem (name Теорема_о_непрерывности_сужения) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_компактности_в_Lp-пространствах> и <Теорема_о_непрерывности_сужения> доказали <Принцип_компактности_в_анализе> (0.94*" (min  ?c1 ?c2) "="(* 0.94 (min ?c1 ?c2))")")))
    (assert (theorem (name Принцип_компактности_в_анализе) (coef (* 0.94 (min ?c1 ?c2)))))
)

(defrule rule_92
(declare (salience 20))
    (theorem (name Принцип_компактности_в_анализе) (coef ?c1))
    (theorem (name Принцип_локальной_компактности) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Принцип_компактности_в_анализе> и <Принцип_локальной_компактности> доказали <Теорема_о_минимуме_в_компактных_множествах> (0.92*" (min  ?c1 ?c2) "="(* 0.92 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_минимуме_в_компактных_множествах) (coef (* 0.92 (min ?c1 ?c2)))))
)

(defrule rule_93
(declare (salience 20))
    (theorem (name Неравенство_Минковского) (coef ?c1))
    (theorem (name Теорема_о_равномерной_сходимости_функций) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Неравенство_Минковского> и <Теорема_о_равномерной_сходимости_функций> доказали <Принцип_вытеснения> (0.69*" (min  ?c1 ?c2) "="(* 0.69 (min ?c1 ?c2))")")))
    (assert (theorem (name Принцип_вытеснения) (coef (* 0.69 (min ?c1 ?c2)))))
)

(defrule rule_94
(declare (salience 20))
    (theorem (name Теорема_о_слабой_сходимости_в_Lp-пространствах) (coef ?c1))
    (theorem (name Признак_Римана_для_абсолютной_сходимости) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_слабой_сходимости_в_Lp-пространствах> и <Признак_Римана_для_абсолютной_сходимости> доказали <Признак_Коши_для_рядов_в_Lp-пространствах> (0.77*" (min  ?c1 ?c2) "="(* 0.77 (min ?c1 ?c2))")")))
    (assert (theorem (name Признак_Коши_для_рядов_в_Lp-пространствах) (coef (* 0.77 (min ?c1 ?c2)))))
)

(defrule rule_95
(declare (salience 20))
    (theorem (name Теорема_о_линейной_непрерывности_оператора) (coef ?c1))
    (theorem (name Лемма_об_интегрируемых_функциях) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_линейной_непрерывности_оператора> и <Лемма_об_интегрируемых_функциях> доказали <Лемма_о_собственных_функциях_оператора> (0.16*" (min  ?c1 ?c2) "="(* 0.16 (min ?c1 ?c2))")")))
    (assert (theorem (name Лемма_о_собственных_функциях_оператора) (coef (* 0.16 (min ?c1 ?c2)))))
)

(defrule rule_96
(declare (salience 20))
    (theorem (name Теорема_о_линейной_непрерывности_оператора) (coef ?c1))
    (theorem (name Теорема_о_равномерной_ограниченности_операторов) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_линейной_непрерывности_оператора> и <Теорема_о_равномерной_ограниченности_операторов> доказали <Теорема_о_проекции_на_подпространство> (0.44*" (min  ?c1 ?c2) "="(* 0.44 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_проекции_на_подпространство) (coef (* 0.44 (min ?c1 ?c2)))))
)

(defrule rule_97
(declare (salience 20))
    (theorem (name Лемма_о_слабой_сходимости) (coef ?c1))
    (theorem (name Принцип_компактности_в_анализе) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Лемма_о_слабой_сходимости> и <Принцип_компактности_в_анализе> доказали <Теорема_о_слабой_компактности_в_Lp-пространствах> (0.66*" (min  ?c1 ?c2) "="(* 0.66 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_слабой_компактности_в_Lp-пространствах) (coef (* 0.66 (min ?c1 ?c2)))))
)

(defrule rule_98
(declare (salience 20))
    (theorem (name Теорема_о_минимуме_в_компактных_множествах) (coef ?c1))
    (theorem (name Лемма_об_интегрируемых_функциях) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_минимуме_в_компактных_множествах> и <Лемма_об_интегрируемых_функциях> доказали <Принцип_максимума> (0.04*" (min  ?c1 ?c2) "="(* 0.04 (min ?c1 ?c2))")")))
    (assert (theorem (name Принцип_максимума) (coef (* 0.04 (min ?c1 ?c2)))))
)

(defrule rule_99
(declare (salience 20))
    (theorem (name Теорема_о_пределе_интегралов_Лебега) (coef ?c1))
    (theorem (name Лемма_о_распределении_предела) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_пределе_интегралов_Лебега> и <Лемма_о_распределении_предела> доказали <Теорема_о_монотонной_сходимости> (0.9*" (min  ?c1 ?c2) "="(* 0.9 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_монотонной_сходимости) (coef (* 0.9 (min ?c1 ?c2)))))
)

(defrule rule_100
(declare (salience 20))
    (theorem (name Теорема_о_компактности_в_Lp-пространствах) (coef ?c1))
    (theorem (name Принцип_локальной_компактности) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_компактности_в_Lp-пространствах> и <Принцип_локальной_компактности> доказали <Теорема_о_вложении_Соболева> (0.89*" (min  ?c1 ?c2) "="(* 0.89 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_вложении_Соболева) (coef (* 0.89 (min ?c1 ?c2)))))
)

(defrule rule_101
(declare (salience 20))
    (theorem (name Признак_Абеля_для_рядов) (coef ?c1))
    (theorem (name Теорема_о_равномерной_сходимости_функций) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Признак_Абеля_для_рядов> и <Теорема_о_равномерной_сходимости_функций> доказали <Теорема_о_равномерной_сходимости_рядов_функций> (0.25*" (min  ?c1 ?c2) "="(* 0.25 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_равномерной_сходимости_рядов_функций) (coef (* 0.25 (min ?c1 ?c2)))))
)

(defrule rule_102
(declare (salience 20))
    (theorem (name Интегрируемость_непрерывных_функций) (coef ?c1))
    (theorem (name Теорема_о_замене_переменной_для_интегралов_Лебега) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Интегрируемость_непрерывных_функций> и <Теорема_о_замене_переменной_для_интегралов_Лебега> доказали <Лемма_об_интегралах_Фубини> (0.91*" (min  ?c1 ?c2) "="(* 0.91 (min ?c1 ?c2))")")))
    (assert (theorem (name Лемма_об_интегралах_Фубини) (coef (* 0.91 (min ?c1 ?c2)))))
)

(defrule rule_103
(declare (salience 20))
    (theorem (name Теорема_о_линейной_непрерывности_оператора) (coef ?c1))
    (theorem (name Принцип_наименьшего_действия) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_линейной_непрерывности_оператора> и <Принцип_наименьшего_действия> доказали <Теорема_о_существовании_решений_для_уравнений_с_частными_производными> (0.6*" (min  ?c1 ?c2) "="(* 0.6 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_существовании_решений_для_уравнений_с_частными_производными) (coef (* 0.6 (min ?c1 ?c2)))))
)

(defrule rule_104
(declare (salience 20))
    (theorem (name Теорема_о_непрерывности_меры) (coef ?c1))
    (theorem (name Теорема_о_слабой_компактности_в_Lp-пространствах) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_непрерывности_меры> и <Теорема_о_слабой_компактности_в_Lp-пространствах> доказали <Теорема_о_плотности_в_пространстве_Lp> (0.59*" (min  ?c1 ?c2) "="(* 0.59 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_плотности_в_пространстве_Lp) (coef (* 0.59 (min ?c1 ?c2)))))
)

(defrule rule_105
(declare (salience 20))
    (theorem (name Теорема_о_существовании_и_единственности_предела) (coef ?c1))
    (theorem (name Теорема_о_непрерывности_суммы_и_произведения_функций) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_существовании_и_единственности_предела> и <Теорема_о_непрерывности_суммы_и_произведения_функций> доказали <Теорема_о_предельном_переходе_в_неравенствах> (0.03*" (min  ?c1 ?c2) "="(* 0.03 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_предельном_переходе_в_неравенствах) (coef (* 0.03 (min ?c1 ?c2)))))
)

(defrule rule_106
(declare (salience 20))
    (theorem (name Теорема_о_существовании_предела_монотонной_ограниченной_последовательности) (coef ?c1))
    (theorem (name Признак_Даламбера) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_существовании_предела_монотонной_ограниченной_последовательности> и <Признак_Даламбера> доказали <Свойства_пределов_произведения> (0.81*" (min  ?c1 ?c2) "="(* 0.81 (min ?c1 ?c2))")")))
    (assert (theorem (name Свойства_пределов_произведения) (coef (* 0.81 (min ?c1 ?c2)))))
)

(defrule rule_107
(declare (salience 20))
    (theorem (name Теорема_о_промежуточных_значениях) (coef ?c1))
    (theorem (name Теорема_об_единственности_предела) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_промежуточных_значениях> и <Теорема_об_единственности_предела> доказали <Формула_Ньютона-Лейбница> (0.89*" (min  ?c1 ?c2) "="(* 0.89 (min ?c1 ?c2))")")))
    (assert (theorem (name Формула_Ньютона-Лейбница) (coef (* 0.89 (min ?c1 ?c2)))))
)

(defrule rule_108
(declare (salience 20))
    (theorem (name Теорема_Больцано-Вейерштрасса) (coef ?c1))
    (theorem (name Свойства_интегралов) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_Больцано-Вейерштрасса> и <Свойства_интегралов> доказали <Существование_и_единственность_решения_дифференциального_уравнения> (0.76*" (min  ?c1 ?c2) "="(* 0.76 (min ?c1 ?c2))")")))
    (assert (theorem (name Существование_и_единственность_решения_дифференциального_уравнения) (coef (* 0.76 (min ?c1 ?c2)))))
)

(defrule rule_109
(declare (salience 20))
    (theorem (name Дифференцируемость_суммы) (coef ?c1))
    (theorem (name Сходимость_интегралов_Римана) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Дифференцируемость_суммы> и <Сходимость_интегралов_Римана> доказали <Свойства_производных> (0.64*" (min  ?c1 ?c2) "="(* 0.64 (min ?c1 ?c2))")")))
    (assert (theorem (name Свойства_производных) (coef (* 0.64 (min ?c1 ?c2)))))
)

(defrule rule_110
(declare (salience 20))
    (theorem (name Интегрируемость_ограниченных_функций) (coef ?c1))
    (theorem (name Признак_сходимости_ряда) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Интегрируемость_ограниченных_функций> и <Признак_сходимости_ряда> доказали <Признак_сравнения_для_рядов> (0.64*" (min  ?c1 ?c2) "="(* 0.64 (min ?c1 ?c2))")")))
    (assert (theorem (name Признак_сравнения_для_рядов) (coef (* 0.64 (min ?c1 ?c2)))))
)

(defrule rule_111
(declare (salience 20))
    (theorem (name Дифференцируемость_произведения) (coef ?c1))
    (theorem (name Интегрируемость_непрерывно_дифференцируемых_функций) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Дифференцируемость_произведения> и <Интегрируемость_непрерывно_дифференцируемых_функций> доказали <Теорема_о_точечной_сходимости_последовательности_функций> (0.03*" (min  ?c1 ?c2) "="(* 0.03 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_точечной_сходимости_последовательности_функций) (coef (* 0.03 (min ?c1 ?c2)))))
)

(defrule rule_112
(declare (salience 20))
    (theorem (name Теорема_о_непрерывности_предела) (coef ?c1))
    (theorem (name Признак_сходимости_интегралов) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_непрерывности_предела> и <Признак_сходимости_интегралов> доказали <Теорема_о_непрерывности_интеграла_по_параметру> (0.49*" (min  ?c1 ?c2) "="(* 0.49 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_непрерывности_интеграла_по_параметру) (coef (* 0.49 (min ?c1 ?c2)))))
)

(defrule rule_113
(declare (salience 20))
    (theorem (name Теорема_о_замене_переменной_в_интеграле) (coef ?c1))
    (theorem (name Теорема_о_предельном_переходе_в_интегралах) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_замене_переменной_в_интеграле> и <Теорема_о_предельном_переходе_в_интегралах> доказали <Признак_Коши_сходимости_интегралов> (0.95*" (min  ?c1 ?c2) "="(* 0.95 (min ?c1 ?c2))")")))
    (assert (theorem (name Признак_Коши_сходимости_интегралов) (coef (* 0.95 (min ?c1 ?c2)))))
)

(defrule rule_114
(declare (salience 20))
    (theorem (name Теорема_о_пределе_ряда_функций) (coef ?c1))
    (theorem (name Теорема_Гаусса-Остроградского) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_пределе_ряда_функций> и <Теорема_Гаусса-Остроградского> доказали <Теорема_о_последовательности_непрерывных_функций> (0.67*" (min  ?c1 ?c2) "="(* 0.67 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_последовательности_непрерывных_функций) (coef (* 0.67 (min ?c1 ?c2)))))
)

(defrule rule_115
(declare (salience 20))
    (theorem (name Теорема_о_характеристическом_свойстве_интеграла) (coef ?c1))
    (theorem (name Теорема_о_дифференцировании_под_знаком_интеграла) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_характеристическом_свойстве_интеграла> и <Теорема_о_дифференцировании_под_знаком_интеграла> доказали <Теорема_о_замене_переменной_в_кратном_интеграле> (0.35*" (min  ?c1 ?c2) "="(* 0.35 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_замене_переменной_в_кратном_интеграле) (coef (* 0.35 (min ?c1 ?c2)))))
)

(defrule rule_116
(declare (salience 20))
    (theorem (name Интеграл_Лебега) (coef ?c1))
    (theorem (name Признак_абсолютной_сходимости) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Интеграл_Лебега> и <Признак_абсолютной_сходимости> доказали <Теорема_о_независимости_порядка_интегрирования_в_условных_интегралах> (0.42*" (min  ?c1 ?c2) "="(* 0.42 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_независимости_порядка_интегрирования_в_условных_интегралах) (coef (* 0.42 (min ?c1 ?c2)))))
)

(defrule rule_117
(declare (salience 20))
    (theorem (name Свойства_функций_класса_C1) (coef ?c1))
    (theorem (name Теорема_о_замене_переменной_для_интегралов_Лебега) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Свойства_функций_класса_C1> и <Теорема_о_замене_переменной_для_интегралов_Лебега> доказали <Лемма_о_слабой_сходимости> (0.46*" (min  ?c1 ?c2) "="(* 0.46 (min ?c1 ?c2))")")))
    (assert (theorem (name Лемма_о_слабой_сходимости) (coef (* 0.46 (min ?c1 ?c2)))))
)

(defrule rule_118
(declare (salience 20))
    (theorem (name Теорема_Вейерштрасса_о_сходимости_ряда_функций) (coef ?c1))
    (theorem (name Лемма_о_распределении_предела) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_Вейерштрасса_о_сходимости_ряда_функций> и <Лемма_о_распределении_предела> доказали <Теорема_о_неравенстве_треугольника_в_Lp-пространствах> (0.36*" (min  ?c1 ?c2) "="(* 0.36 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_неравенстве_треугольника_в_Lp-пространствах) (coef (* 0.36 (min ?c1 ?c2)))))
)

(defrule rule_119
(declare (salience 20))
    (theorem (name Теорема_о_преобразовании_Фурье) (coef ?c1))
    (theorem (name Свойства_градиента) (coef ?c2))
    =>
    (assert( appendmessage (str-cat "Из <Теорема_о_преобразовании_Фурье> и <Свойства_градиента> доказали <Теорема_о_минимуме_в_компактных_множествах> (0.8*" (min  ?c1 ?c2) "="(* 0.8 (min ?c1 ?c2))")")))
    (assert (theorem (name Теорема_о_минимуме_в_компактных_множествах) (coef (* 0.8 (min ?c1 ?c2)))))
)

(defrule rule_120
(declare (salience 20))
    (theorem (name Формула_Ньютона-Лейбница) (coef ?c1))
    =>
    (assert( appendmessage (str-cat "Из <Формула_Ньютона-Лейбница> доказали <Полнота_действительных_чисел> (0.31*" (min  ?c1) "="(* 0.31 (min ?c1))")")))
    (assert (theorem (name Полнота_действительных_чисел) (coef (* 0.31 (min ?c1)))))
)
