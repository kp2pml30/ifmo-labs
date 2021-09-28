package info.kgeorgiy.ja.prokopenko.statistics;

import java.text.*;
import java.util.Locale;
import java.util.Comparator;

public class Dumpers {
    private Dumpers() {
    }

    private static class BreakingDumper implements StatisticParser<String, Double> {
        private final BreakIterator breakIterator;
        private final Comparator<? super String> comparator;

        public BreakingDumper(Locale locale, BreakIterator breakIterator) {
            comparator = Collator.getInstance(locale);
            this.breakIterator = breakIterator;
        }

        protected void add(String text) {

        }

        @Override
        public Statistics<String, Double> parse(final String str) {
            breakIterator.setText(str);
            int start = breakIterator.first();
            for (int end = breakIterator.next(); end != BreakIterator.DONE; start = end, end = breakIterator.next()) {
                add(str.substring(start, end));
            }
            return null;
        }
    }

    public static StatisticParser<String, Double> wordCounter(Locale locale) {
        return new BreakingDumper(locale, BreakIterator.getSentenceInstance(locale));
    }
}
