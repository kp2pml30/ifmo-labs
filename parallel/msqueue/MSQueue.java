package msqueue;

import kotlinx.atomicfu.AtomicRef;

public class MSQueue implements Queue {
    private final AtomicRef<Node> head;
    private final AtomicRef<Node> tail;

    public MSQueue() {
        final Node dummy = new Node(Integer.MAX_VALUE);
        this.head = new AtomicRef<>(dummy);
        this.tail = new AtomicRef<>(dummy);
    }

    @Override
    public void enqueue(final int x) {
        final Node newTail = new Node(x);
        final Pointer newTailPtr = new Pointer(newTail);
        while (true) {
            final Node tail = this.tail.getValue();
            final Pointer next = tail.ptr.getValue();
            if (this.tail.getValue() != tail) { // reference comparison
                continue;
            }
            if (next.node != null) {
                this.tail.compareAndSet(tail, next.node); // try to advance
                continue;
            }
            if (tail.ptr.compareAndSet(next, newTailPtr)) {
                break;
            }
        }
    }

    private int dequeuePeek(final boolean take) {
        while (true) {
            final Node head = this.head.getValue();
            final Node tail = this.tail.getValue();
            final Pointer next = head.ptr.getValue();
            if (head != this.head.getValue()) {
                continue;
            }
            if (head.ptr == tail.ptr) { // reference comparison
                if (next.node == null) {
                    return Integer.MIN_VALUE; // empty queue
                }
                this.tail.compareAndSet(tail, next.node); // tail is outdated
                continue;
            }
            final int result = next.node.x;
            if (!take) {
                return result;
            }
            if (this.head.compareAndSet(head, next.node)) {
                return result;
            }
        }
    }

    @Override
    public int dequeue() {
        return dequeuePeek(true);
    }

    @Override
    public int peek() {
        return dequeuePeek(false);
    }

    // indirection class for reference comparison (instead of {@code version})
    private static class Pointer {
        final Node node;

        public Pointer(final Node node) {
            this.node = node;
        }
    }

    private static class Node {
        final int x;
        final AtomicRef<Pointer> ptr;

        public Node(final int x) {
            this(x, new Pointer(null));
        }

        public Node(final int x, final Pointer ptr) {
            this.x = x;
            this.ptr = new AtomicRef<>(ptr);
        }
    }
}