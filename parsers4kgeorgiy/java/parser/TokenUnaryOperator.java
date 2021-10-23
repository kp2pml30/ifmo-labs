package expression.parser;
import expression.CommonExpression;
import expression.UnaryOperator;
import java.lang.reflect.*;

public class TokenUnaryOperator<T> extends Token<T> {
    private final UnaryOperator.Provider<T> operatorProvider;
    public TokenUnaryOperator(int position, UnaryOperator.Provider<T> operatorProvider) {
        super(position, TokenType.UNARYOPERATOR);
        this.operatorProvider = operatorProvider;
    }

    public CommonExpression<T> provide(CommonExpression<T> me) {
        return operatorProvider.provide(me);
    }
}
