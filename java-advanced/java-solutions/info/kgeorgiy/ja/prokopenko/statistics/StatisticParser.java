package info.kgeorgiy.ja.prokopenko.statistics;

public interface StatisticParser<T, Average> {
    Statistics<T, Average> parse(String str);
}
