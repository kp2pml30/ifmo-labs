public class Main {
    static void s(byte[] a1, int a2) {
        int v5 = a1.length;

        for(int i = 0; i < v5 - a2; i += a2) {
            byte v2 = a1[i];
            a1[i] = a1[i - 1 + a2];
            a1[i - 1 + a2] = v2;
        }

    }

    public static void main(String[] args) {
        String a = "bpoctifh_t{tmkh_smowsllsfoe_smia_amsart_h'i?ti_in}";
        if (a.length() <= 128) {
            byte[] dest = a.getBytes();
            for (int i = 2; i <= 10; i++) {
                s(dest, i);
            }
            System.out.println(new String(dest));
        } else {
            System.out.println("String is too long");
        }
    }
}