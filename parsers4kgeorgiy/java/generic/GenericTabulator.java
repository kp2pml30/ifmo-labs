package expression.generic;

import java.math.BigInteger;

import expression.parser.*;
import expression.parser.error.ParserException;
import expression.CommonExpression;
import expression.exceptions.EvaluationException;

public class GenericTabulator implements Tabulator {
    private <T> Object[][][] tabulateImpl(NumberWrapperProvider<T> provider, String expression, int x1, int x2, int y1, int y2, int z1, int z2) throws ParserException {
        Object[][][] ret = new Object[x2 - x1 + 1][y2 - y1 + 1][z2 - z1 + 1];
        Tokenizer<T> tokenizer = new Tokenizer<T>(expression, provider);
        Parser<T> parser = new ExpressionParser<T>();
        CommonExpression<T> expr = parser.parse(tokenizer);
        for (int x = x1; x <= x2; x++) {
            for (int y = y1; y <= y2; y++) {
                for (int z = z1; z <= z2; z++) {
                    try {
                        ret[x - x1][y - y1][z - z1] = expr.evaluate(provider.provide(x), provider.provide(y), provider.provide(z)).get();
                    } catch (ArithmeticException e) {
                        ret[x - x1][y - y1][z - z1] = null;
                    }
                }
            }
        }
        return ret;
    }

    /* pre : i2 >= i1 for i in {x, y, z}
     * pre : mode i/d/bi
     */
    @Override
    public Object[][][] tabulate(String mode, String expression, int x1, int x2, int y1, int y2, int z1, int z2) throws Exception {
        switch (mode) { //:NOTE: зачем оборачить все во wrapper?  Можно избавиться и от враппера и от провайдера
        case "i":
            return this.<Integer>tabulateImpl(new IntegerWrapper.Provider(), expression, x1, x2, y1, y2, z1, z2);
        case "d":
            return this.<Double>tabulateImpl(new DoubleWrapper.Provider(), expression, x1, x2, y1, y2, z1, z2);
        case "bi":
            return this.<BigInteger>tabulateImpl(new BigIntegerWrapper.Provider(), expression, x1, x2, y1, y2, z1, z2);
        default:
            throw new IllegalArgumentException("Unknown mode");
        }
    }
}
