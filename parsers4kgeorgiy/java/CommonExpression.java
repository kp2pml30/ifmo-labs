package expression;

public interface CommonExpression<T> extends Expression<T>, TripleExpression<T> {
    void toString(StringBuilder builder);
    void toMiniString(StringBuilder builder);
    @Override
    default String toMiniString() {
        StringBuilder builder = new StringBuilder();
        toMiniString(builder);
        return builder.toString();
    }
}
