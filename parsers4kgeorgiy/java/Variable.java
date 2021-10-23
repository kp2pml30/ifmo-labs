package expression;

import java.util.Objects;

import expression.generic.NumberWrapper;

public class Variable<T> implements Value<T> {
    private final String name;
    public Variable(final String name) {
        if (!Objects.equals(name, "x") && !Objects.equals(name, "y") && !Objects.equals(name, "z")) {
            throw new IllegalArgumentException("only x, y, z variables are supported -- " + name);
        }
        this.name = name;
    }

    public NumberWrapper<T> evaluate(NumberWrapper<T> x) {
        return x;
    }

    @Override
    public NumberWrapper<T> evaluate(NumberWrapper<T> x, NumberWrapper<T> y, NumberWrapper<T> z) {
        switch (name) {
        case "x":
            return x;
        case "y":
            return y;
        case "z":
            return z;
        default:
            throw new RuntimeException("Wrong variable name : " + name);
        }
    }

    @Override
    public String toString() {
        return name;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj instanceof Variable) {
            return name.equals(((Variable)obj).name);
        }
        return false;
    }

    @Override
    public int hashCode() {
        return name.hashCode();
    }
}

