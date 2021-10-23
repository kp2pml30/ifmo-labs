package expression;

public interface Value<T> extends CommonExpression<T> {
    @Override
    default void toString(StringBuilder builder) {
        builder.append(toString());
    }

    @Override
    default String toMiniString() {
        StringBuilder builder = new StringBuilder();
        toMiniString(builder);
        return builder.toString();
    }

    @Override
    default void toMiniString(StringBuilder builder) {
        builder.append(toString());
    }
}
