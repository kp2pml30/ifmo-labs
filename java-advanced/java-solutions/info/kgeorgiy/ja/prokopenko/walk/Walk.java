package info.kgeorgiy.ja.prokopenko.walk;

import java.lang.RuntimeException;
import java.lang.UnsupportedOperationException;
import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.NoSuchFileException;
import java.nio.file.InvalidPathException;
import java.nio.file.FileAlreadyExistsException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.nio.file.Path;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.FileVisitResult;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.stream.Stream;
import java.io.BufferedWriter;
import java.io.BufferedInputStream;
import java.io.InputStream;

public class Walk {
	protected BufferedWriter ostream;
	String fileName;

	public Walk(BufferedWriter out, String fileName) {
		if (out == null) {
			throw new RuntimeException("output stream is null");
		}
		ostream = out;
		this.fileName = fileName;
	}
	public Walk(BufferedWriter out) {
		this(out, null);
	}

	public interface WalkerProvider {
		Walk provide(BufferedWriter writer, String fname);
	}

	protected static void printError(String fname, String error, Exception e) {
		System.err.format("error in \"%s\" : %s\n", fname, error);
		if (e != null) {
			System.err.println("Exception info: ");
			System.err.println(e);
		}
	}

	public static long calcPJW(InputStream strm) throws IOException {
		long hash = 0;
		final byte[] buf = new byte[4096];
		while (true) {
			int read = strm.read(buf);
			if (read == -1) {
				return hash;
			}
			for (int i = 0; i < read; i++) {
				int c = Byte.toUnsignedInt(buf[i]);
				hash = (hash << 8) + c;
				long h = hash & 0xff00000000000000L;
				hash ^= h >> (64 * 3 / 4);
				hash &= ~h;
			}
		}
	}

	protected void printFileAndHash(long pjw, String path) {
		try {
			ostream.write(String.format("%016x %s", pjw, path));
			ostream.write(System.lineSeparator());
		} catch (IOException e) {
				printError(fileName, "write error", e);
		}
	}

	protected void createDir(String path) {
		Path p = Paths.get(path).getParent();
		if (p == null || p.equals("")) {
			return;
		}
		try {
			Files.createDirectories(p);
		} catch (Exception e) {
			printError(p.toString(), "can't create directory", e);
		}
	}

	protected void process(String path) {
		boolean strmInitialized = false;
		long pjw = 0;
		try (var strm = Files.newInputStream(Paths.get(path))) {
			strmInitialized = true;
			try {
				pjw = calcPJW(strm);
			} catch (IOException e) {
				printError(path, "read error, setting hash to zero", e);
			}
		} catch (NoSuchFileException e) {
			System.err.println("no file " + path);
			createDir(path);
		} catch (InvalidPathException e) {
			printError(path, "wrong path", e);
		} catch (IOException e) {
			if (!strmInitialized) {
				printError(path, "can't open file", e);
			} else {
				printError(path, "read error", e);
			}
		}

		printFileAndHash(pjw, path);
	}

	protected static void start(String in, String out, WalkerProvider provider) {
		boolean ostrmInitialized = false;
		boolean istrmInitialized = false;
		// are we allowed to use var?
		try (var ostrm = Files.newBufferedWriter(Paths.get(out))) {
			ostrmInitialized = true;
			try (var istrm = Files.lines(Paths.get(in))) {
				istrmInitialized = true;
				var walker = provider.provide(ostrm, out);
				try {
					istrm.forEach((String s) -> walker.process(s));
				} catch (UncheckedIOException e) {
					printError(in, "read error", e.getCause());
				}
			}
		} catch (IOException | InvalidPathException e) {
			if (!ostrmInitialized) {
				printError(out, "output stream initialization failed", e);
			} else if (!istrmInitialized) {
				printError(in, "can't crete input stream", e);
			} else {
				printError("<unknown>", "IO error occured, possibly in close", e);
			}
		}
	}

	protected static boolean checkArgs(String[] args) {
		if (args == null || args.length < 2 || args[0] == null || args[1] == null) {
			return false;
		}
		if (args.length != 2) {
			System.err.println("expected 2 arguments, rest ignored");
		}
		return true;
	}

	public static void main(String[] args) {
		if (!checkArgs(args)) {
			System.err.println("expected 2 arguments: <in-file> <out-file>");
			return;
		}
		start(args[0], args[1], (x, s) -> new Walk(x, s));
	}
}
