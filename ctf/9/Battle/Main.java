/*
decompile
run
generates file.jar
decompile)
inline
find resources `array`, xml
*/

import java.io.*;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Base64;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

class C0000A {

    /* renamed from: z */
    // private Resources f0z;

    /* renamed from: a */
    public void mo1a() {
        // this.f0z = r;
    }

    /* renamed from: b */
    public String[] mo2b(int i) {
        return new String[] {
                "zcrPrQ==",
                "paWtzsvPzw==",
                "pcfPzw==",
                "vpGbjZCWmw==",
                "pafSya0=",
                "pc7Pz88=",
                "pafSzs8=",
                "tLOnzs7P",
                "jIqPzI0=",
                "uq3SyZE=",
                "qZqNjIaM",
            };
        // return this.f0z.getStringArray(i);
    }

    /* renamed from: c */
    public int[] mo3c(int i) {
        // fetched from res dir
        return new int[] {3, 8};
        // return this.f0z.getIntArray(i);
    }
}

class C0001B extends C0000A {
    /* renamed from: a */
    public static String m3a(String s) {
        byte[] b = Base64.getDecoder().decode(s);
        for (int i = 0; i < b.length; i++) {
            b[i] = (byte) (b[i] ^ 255);
        }
        return new String(b);
    }

    /* renamed from: b */
    public static String m4b(String s1, String s2) {
        return String.valueOf(s1) + " " + s2 + " Green";
    }
}

class C0002C extends C0001B {

    /* renamed from: aa */
    private C0000A f1aa;

    /* renamed from: bb */
    private String f2bb;

    /* renamed from: a */
    public void mo4a(int i1, int i2) {
        this.f1aa = new C0000A();
        this.f1aa.mo1a(); // getResources()
        this.f2bb = C0001B.m4b(C0001B.m3a(this.f1aa.mo2b(i2)[this.f1aa.mo3c(i1)[0]]), C0001B.m3a(this.f1aa.mo2b(i2)[this.f1aa.mo3c(i1)[1]]));
    }

    /* renamed from: b */
    public String mo5b(String s) {
        System.out.println(this.f2bb);
        if (s.equals(this.f2bb)) {
            return "Correct!";
        }
        return "Wrong!";
    }
}

public class Main {
    private C0002C asd;

    public static String b64e(String str) {
        byte[] decode = Base64.getDecoder().decode(str);
        for (int i = 0; i < decode.length; i++) {
            decode[i] = (byte) (decode[i] ^ 255);
        }
        String ret = new String(decode);
        System.out.println(str + " --> " + ret);
        return ret;
    }

    public static final int RKappa = 2130837504;
    public static final int RKek = 2130837505;

    public void onCreate() throws Exception {
        InputStream open = Files.newInputStream(Paths.get(b64e("mZaTmtGdlpE=")));
        byte[] bArr = new byte[open.available()];
        open.read(bArr);
        for (int i = 0; i < bArr.length; i++) {
            bArr[i] = (byte) (bArr[i] ^ 237);
        }
        open.close();
        File file = new File(".", b64e("mZaTmtGVno0="));
        BufferedOutputStream bufferedOutputStream = new BufferedOutputStream(new FileOutputStream(file));
        bufferedOutputStream.write(bArr);
        bufferedOutputStream.close();
        Class<?> cls = Main.class.getClassLoader().getClass(); // Class.forName(b64e("m56TiZaU0YyGjIuaktG7moe8k56MjLOQnpuajQ=="));

        /*
        Constructor<?> constructor = cls.getConstructor(String.class, String.class, String.class, ClassLoader.class);
        Object[] objArr = new Object[4];
        objArr[0] = file.getCanonicalPath();
        objArr[1] = ".";
        objArr[3] = ClassLoader.getSystemClassLoader();
        Object newInstance = constructor.newInstance(objArr);
        */
        Object newInstance = Main.class.getClassLoader();
        // this.asd = (Class) cls.getMethod(b64e("k5Cem7yTnoyM"), String.class).invoke(newInstance, b64e("nJCS0ZqHnpKPk5rRj56MjIiQjZvRvA=="));
        this.asd = new C0002C();
        this.asd.mo4a(RKappa, RKek);
    }

    public void main1() throws Exception {
        String test = "Android sup3r Green";
        System.out.println((String)this.asd.mo5b(test));
    }

    public static void main(String[] args) throws Exception {
        Main m = new Main();
        m.onCreate();
        m.main1();
    }
}
