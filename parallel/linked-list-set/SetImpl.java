package linked_list_set;

import kotlinx.atomicfu.AtomicRef;

public class SetImpl implements Set {
    private static class Node {
        final AtomicRef<Object> next;
        final int x;

        Node(final int x, final Object next) {
            this.x = x;
            this.next = new AtomicRef<>(next);
        }
    }

    private static class Removed {
        final Node node;

        Removed(final Node node) {
            this.node = node;
        }
    }

    private static class Window {
        final Node cur;
        final Node next;
        final Node after;

        Window(final Node cur, final Node next, final Node after) {
            this.cur = cur;
            this.next = next;
            this.after = after;
        }
    }

    private final Node head = new Node(Integer.MIN_VALUE, new Node(Integer.MAX_VALUE, null));

    /**
     * Returns the {@link Window}, where cur.x < x <= next.x
     */
    private Window findWindow(int x) {
        retry: while (true) {
            Node cur = head;
            Node next = (Node)head.next.getValue(); // head is not deleted
            while (true) {
                final Object an = next.next.getValue();
                if (an instanceof Removed) {
                    final Removed afterNext = (Removed)an;
                    cur.next.compareAndSet(next, afterNext.node);
                    continue retry;
                } else {
                    final Node afterNext = (Node)an;
                    if (cur.x < x && x <= next.x) {
                        return new Window(cur, next, afterNext);
                    }
                    cur = next;
                    next = afterNext;
                }
            }
        }
    }

    private void checkKey(final int x) {
        if (x == Integer.MIN_VALUE || x == Integer.MAX_VALUE) {
            throw new IllegalArgumentException();
        }
    }

    @Override
    public boolean add(final int x) {
        checkKey(x);
        while (true) {
            final Window w = findWindow(x);
            if (w.next.x == x) {
                return false;
            }
            if (w.cur.next.compareAndSet(w.next, new Node(x, w.next))) {
                return true;
            }
        }
    }

    @Override
    public boolean remove(int x) {
        checkKey(x);
        while (true) {
            final Window w = findWindow(x);
            if (w.next.x != x) {
                return false;
            }
            if (w.next.next.compareAndSet(w.after, new Removed(w.after))) {
                w.cur.next.compareAndSet(w.next, w.after);
                return true;
            }
        }
    }

    @Override
    public boolean contains(int x) {
        final Window w = findWindow(x);
        return w.next.x == x;
    }
}