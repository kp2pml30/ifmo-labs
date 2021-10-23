package expression;

import java.util.Set;
import java.util.Objects;

public class BinaryMinifier {
    private static class Pair {
        public Class<?> left, right;
        public Pair(Class<?> l, Class<?> r) {
            left = l;
            right = r;
        }
        @Override
        public boolean equals(Object obj) {
            if (!(obj instanceof Pair)) {
                return false;
            }
            Pair to = (Pair)obj;
            return Objects.equals(left, to.left) && Objects.equals(right, to.right);
        }
        @Override
        public int hashCode() {
            return 1;
        }
    }
    private static final Set<Pair> possible = Set.of(new Pair(Add.class, Subtract.class));
    public static boolean mayBeMinified(Class<?> left, Class<?> right) {
        return possible.contains(new Pair(left, right));
    }
}