import java.nio.charset.StandardCharsets;
import java.util.Base64;

public class Main {
    private static byte sumOfXors(int to, byte w) {
        byte res = 0;
        for (int i = 1; i <= to; i++) {
            res ^= w * i;
        }
        return res;
    }

    public static void main(String[] args) {
        byte[] flag = args[0].getBytes();
        byte[] immutDecode = Base64.getDecoder().decode("6enp6enp6enp6enp6enp6enp6enp6eml6urq6unq6erp6urq6urq6urq6enp6unq6enp6unq6erp6enq6enp6unp6erp6erq6urq6urq6urq6urp6unp6enq6erq6unp6enp6unq6enp6unp6enp6unq6erq6urq6unp6urq6erq6unp6erp6unp6enp6erp6enp6enp6enp6enq6urp6urq6urq6urq6urq6erqsunp6unp6erp6unp6enp6enp6enq6enp6erq6unq6erq6urq6urq6urq6urp6enp6enp6enp6enp6enp6enp6enp6ek=");
        System.out.print("[");
        for (int i = 0; i < immutDecode.length; i++) {
            immutDecode[i] = (byte) (immutDecode[i] ^ 202);
            System.out.print(immutDecode[i] + ",");
            if (immutDecode[i] == 120) {
                // System.out.println("120 at " + i); // 174
                // 174 = 22 * 7 + 20
                // 6 d 19 r
            }
        }
        System.out.println("]");
        byte[] decode2 = Base64.getDecoder().decode("h4SWl4CSvbIOBxLhtau1qZmnq5WODwgBq5WoorSpr6KZr7WZowcVv7s=");
        int mulBy = 1;
        int padding = 1;
        for (int iOuter = 0; iOuter < flag.length; iOuter++) {
            // flag chooses action
            if (flag[iOuter] == 68) { // D
                // decode2[iOuter] ^= sumOfXors(34, (byte)239);
                decode2[iOuter] ^= 113;
                mulBy++;
            } else if (flag[iOuter] == 82) { // R
                // decode2[iOuter] ^= sumOfXors(34, (byte)97);
                decode2[iOuter] ^= 67;
                padding++;
            } else if (flag[iOuter] == 76) { // L
                // decode2[iOuter] ^= sumOfXors(34, (byte)65);
                decode2[iOuter] ^= (byte)-29;
                padding--;
            } else if (flag[iOuter] == 85) { // U
                // decode2[iOuter] ^= sumOfXors(34, (byte)65);
                decode2[iOuter] ^= (byte)-29;
                mulBy--;
            } else {
                // decode2[iOuter] ^= sumOfXors(34, (byte)65);
                decode2[iOuter] ^= (byte)-29;
            }
            // without flag
            int testAt = (mulBy * 22) + padding;
            if (immutDecode[testAt] == 32 || immutDecode[testAt] == 120 || immutDecode[testAt] == 111) {
                // decode2[iOuter] ^= sumOfXors(34, (byte)67);
                decode2[iOuter] ^= (byte)-123;
            } else {
                for (int i = 1; i <= 41; i++) {
                    decode2[i - 1] ^= (byte)(i * 69);
                }
            }
        }
        System.out.println(immutDecode[(mulBy * 22) + padding]);
        System.out.println(new String(decode2, StandardCharsets.UTF_8));
    }
}
