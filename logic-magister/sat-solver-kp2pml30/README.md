[![Review Assignment Due Date](https://classroom.github.com/assets/deadline-readme-button-24ddc0f5d75046c5622901739e7c5dd533143b0c8e959d652212380cedb1ea36.svg)](https://classroom.github.com/a/4F9VZ0wb)
Нужно реализовать свой SAT-решатель на основе алгоритма DPLL.

Реализацию следует начать с `raise NotImplementedError()` в файле [`solver.py`](solver.py).
Так как ваш код будет запускаться в отдельном потоке с ограничением по времени, не забывайте в реализации
регулярно проверять `self.sigkill.is_set()`, и, если он возвращает `True`, ваш код должен завершить работу
(через `return SATSolverResult.UNKNOWN`).
 
## Условия принятия

Ваш код будет запускаться на тестах в GitHub Actions после каждого push на GitHub.
Вы можете запустить тесты локально, вызвав `python solver_test.py`.
После исполнения будет напечатано примерно следующее:

```
Your solver RANK: 68.2178617730
Your score for this homework: 6 points
```

Первое число (`68.2...`) - **ранк** вашего SAT-решателя. Чем он меньше, тем лучше.
На основании него высчитывается второе число (`6 points`) - **ваша оценка за эту домашку**.

### Об оценивании

- Как вычисляется оценка описано в функции `test_dpll`
- Максимально возможное число баллов за решение - 20
  - см. также раздел *"Дополнительные баллы"* ниже
- Проходное число баллов - 5 (если за эту домашку набрано меньше этого числа баллов, к зачёту нет допуска)

### Ограничения
- если в коде реализован не DPLL (или его вариации, например, с 2-watch-literals или CDCL), домашка **не засчитывается**
- использовать сторонние библиотеки (например, `numpy`) запрещено

## Дополнительные баллы: соревнования

- На основе ранков ваших решателей среди решений, сданных до дедлайна и имеющих ранк `<= 60`, проводятся соревнования
- Топ-3 решения (с наименьшими ранками) получат **ещё + 10 баллов** за эту домашку

## Как вычисляется ранк

(см. функцию `test_folder` в [`solver_test.py`](solver_test.py))

Ранк основан на времени работы вашего решателя. Изначально он равен нулю.
Для каждого бенчмарка происходит следующее.
Решатель запускается с лимитом по времени `TIME_LIMIT` (сейчас: 10 секунд).

- Если решатель вернул `UNKNOWN` или время его работы превзошло лимит по времени, к ранку добавляется `TIME_LIMIT`.
- Если решатель вернул правильное значение (`sat` для выполнимого бенчмарка или `unsat` для невыполнимого), то
к ранку добавляется время его работы.
- Если решатель вернул неправильное значение (`unsat` для выполнимого бенчмарка или `sat` для невыполнимого), то
к ранку добавляется `TIME_LIMIT * 4`.