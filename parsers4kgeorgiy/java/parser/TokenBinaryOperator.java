package expression.parser;
import expression.CommonExpression;
import expression.BinaryOperator;
import expression.Const;
import java.lang.reflect.*;

public class TokenBinaryOperator<T> extends Token<T> {
    private final BinaryOperator.Provider<T> provider;

    public TokenBinaryOperator(int position, BinaryOperator.Provider<T> provider) {
        super(position, TokenType.BINARYOPERATOR);
        this.provider = provider;
    }

    public int getPriority() {
        return provider.getOperatorPriority();
    }

    public CommonExpression<T> provide(CommonExpression<T> left, CommonExpression<T> right) {
        return provider.provide(left, right);
    }
}
