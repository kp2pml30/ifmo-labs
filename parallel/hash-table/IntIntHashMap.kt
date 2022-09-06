import kotlinx.atomicfu.AtomicIntArray
import kotlinx.atomicfu.AtomicRef
import kotlinx.atomicfu.atomic

/**
 * Int-to-Int hash map with open addressing and linear probes.
 *
 * TODO: This class is **NOT** thread-safe.
 */
class IntIntHashMap {
    private val core = atomic(Core(INITIAL_CAPACITY))

    /**
     * Returns value for the corresponding key or zero if this key is not present.
     *
     * @param key a positive key.
     * @return value for the corresponding or zero if this key is not present.
     * @throws IllegalArgumentException if key is not positive.
     */
    operator fun get(key: Int): Int {
        require(key > 0) { "Key must be positive: $key" }
        return toValue(core.value.getInternal(key))
    }

    /**
     * Changes value for the corresponding key and returns old value or zero if key was not present.
     *
     * @param key   a positive key.
     * @param value a positive value.
     * @return old value or zero if this key was not present.
     * @throws IllegalArgumentException if key or value are not positive, or value is equal to
     * [Integer.MAX_VALUE] which is reserved.
     */
    fun put(key: Int, value: Int): Int {
        require(key > 0) { "Key must be positive: $key" }
        require(isValue(value)) { "Invalid value: $value" }
        return toValue(putAndRehashWhileNeeded(key, value))
    }

    /**
     * Removes value for the corresponding key and returns old value or zero if key was not present.
     *
     * @param key a positive key.
     * @return old value or zero if this key was not present.
     * @throws IllegalArgumentException if key is not positive.
     */
    fun remove(key: Int): Int {
        require(key > 0) { "Key must be positive: $key" }
        return toValue(putAndRehashWhileNeeded(key, DEL_VALUE))
    }

    private fun putAndRehashWhileNeeded(key: Int, value: Int): Int {
        while (true) {
            val oldCore = core.value
            val oldValue = oldCore.putInternal(key, value)
            if (oldValue != NEEDS_REHASH) {
                return oldValue
            }
            core.compareAndSet(oldCore, oldCore.rehash())
        }
    }

    private class Core internal constructor(capacity: Int) {
        // Pairs of <key, value> here, the actual
        // size of the map is twice as big.
        val map = AtomicIntArray(2 * capacity)
        val next : AtomicRef<Core?> = atomic(null)
        val shift: Int

        init {
            val mask = capacity - 1
            assert(mask > 0 && mask and capacity == 0) { "Capacity must be power of 2: $capacity" }
            shift = 32 - Integer.bitCount(mask)
        }

        fun getInternal(key: Int): Int {
            while (true) {
                var index = index(key)
                var probes = 0
                while (true) { // optimize for successful lookup
                    val curKey = map[index].value
                    if (curKey == key) {
                        break
                    }
                    if (curKey == NULL_KEY) {
                        return NULL_VALUE
                    }
                    if (++probes >= MAX_PROBES) {
                        return NULL_VALUE
                    }
                    if (index == 0) {
                        index = map.size
                    }
                    index -= 2
                }
                // found key -- return value
                val ret = map[index + 1].value
                if (ret == MOVED) {
                    return next.value!!.getInternal(key)
                }
                assert(!isMoving(NULL_VALUE))
                if (ret == NULL_VALUE || ret == DEL_VALUE) {
                    return NULL_VALUE
                }
                if (isMoving(ret)) {
                    return unMoving(ret)
                }
                return ret
            }
        }

        private fun putInternal(key : Int, value : Int, strict : Boolean) : Int {
            assert(key != NULL_KEY)
            var index = index(key)
            var probes = 0
            while (true) {
                val curKey = map[index].value
                if (curKey == key) {
                    break
                }
                if (curKey == NULL_KEY) { // not found -- claim this slot
                    if (value == DEL_VALUE) {
                        return NULL_VALUE // remove of missing item, no need to claim slot
                    }
                    if (map[index].compareAndSet(curKey, key)) {
                        break
                    } else {
                        continue
                    }
                }
                if (++probes >= MAX_PROBES) {
                    assert(strict)
                    return NEEDS_REHASH
                }
                if (index == 0) {
                    index = map.size
                }
                index -= 2
            }
            // found key -- update value
            assert(map[index].value == key)
            while (true) {
                val ret = map[index + 1].value
                if (ret == MOVED) {
                    return next.value!!.putInternal(key, value, strict)
                }
                if (ret != DEL_VALUE && isMoving(ret)) {
                    pushForward(index)
                    return next.value!!.putInternal(key, value, strict)
                }
                if (!strict && ret != NULL_VALUE) { // in non-strict mode we move only not-NULL
                    return -30
                }
                if (map[index + 1].compareAndSet(ret, value)) {
                    return ret
                }
            }
        }

        fun putInternal(key: Int, value: Int) : Int = putInternal(key, value, true)

        fun rehash() : Core {
            val created = Core(map.size * 2)
            val newCore =
                if (next.compareAndSet(null, created)) {
                    created
                } else {
                    next.value!!
                }
            for (index in 0 until map.size step 2) {
                pushForward(index)
            }
            return newCore
        }

        private fun pushForward(index : Int) {
            while (true) {
                val nxt = next.value ?: return
                val v = map[index + 1].value
                assert(DEL_VALUE != MOVED)
                assert(NULL_VALUE != MOVED)
                if (v == DEL_VALUE || v == NULL_VALUE) {
                    if (map[index + 1].compareAndSet(v, MOVED)) {
                        return
                    }
                    continue
                }
                if (v == MOVED) {
                    return
                }
                // already moving or successfully set to moving
                if (!isMoving(v) && !map[index + 1].compareAndSet(v, makeMoving(v))) {
                    continue
                }
                val k = map[index].value
                assert(k != NULL_KEY)
                nxt.putInternal(k, unMoving(v), false)
                // fails if and only if someone already helped us
                map[index + 1].compareAndSet(makeMoving(v), MOVED)
                return
            }
        }

        /**
         * Returns an initial index in map to look for a given key.
         */
        fun index(key: Int): Int = (key * MAGIC ushr shift) * 2
    }
}

private const val MAGIC = -0x61c88647 // golden ratio
private const val INITIAL_CAPACITY = 2 // !!! DO NOT CHANGE INITIAL CAPACITY !!!
private const val MAX_PROBES = 8 // max number of probes to find an item
private const val NULL_KEY = 0 // missing key (initial value)
private const val NULL_VALUE = 0 // missing value (initial value)
private const val DEL_VALUE = Int.MAX_VALUE // mark for removed value
private const val NEEDS_REHASH = -1 // returned by `putInternal` to indicate that rehash is needed

private const val MOVED = Integer.MIN_VALUE
private const val highBit : Int = 0x80000000.toInt()
private const val notHighBit : Int = highBit.inv()

private fun makeMoving(value : Int) = value or highBit
private fun isMoving(value : Int) : Boolean {
    assert(value != MOVED)
    assert(value != DEL_VALUE)
    return (value and highBit) != 0
}
private fun unMoving(value : Int) = value and notHighBit

// Checks is the value is in the range of allowed values
private fun isValue(value: Int): Boolean = value in (1 until DEL_VALUE)

// Converts internal value to the public results of the methods
private fun toValue(value: Int): Int = if (isValue(value)) value else 0