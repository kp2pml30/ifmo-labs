/**
 * В теле класса решения разрешено использовать только переменные делегированные в класс RegularInt.
 * Нельзя volatile, нельзя другие типы, нельзя блокировки, нельзя лазить в глобальные переменные.
 *
 * @author Prokopenko Kirill
 *
 * 5th page of https://lamport.azurewebsites.net/pubs/lamport-concurrent-clocks.pdf
 * plus generalization
 */
class Solution : MonotonicClock {
    private var c1o by RegularInt(0)
    private var c1n by RegularInt(0)
    private var c2o by RegularInt(0)
    private var c2n by RegularInt(0)
    private var c3 by RegularInt(0)

    override fun write(time: Time) {
        c1n = time.d1
        c2n = time.d2
        c3 = time.d3
        c2o = time.d2
        c1o = time.d1
    }

    override fun read(): Time {
        val d1o: Int = c1o
        val d2o: Int = c2o
        val d3: Int = c3
        val d2n: Int = c2n
        val d1n: Int = c1n
        if (d1n != d1o) {
            return Time(d1n, 0, 0)
        }
        if (d2n != d2o) {
            return Time(d1n, d2n, 0)
        }
        return Time(d1n, d2n, d3)
    }
}