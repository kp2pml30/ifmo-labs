package info.kgeorgiy.ja.prokopenko.walk;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.NoSuchFileException;
import java.nio.file.InvalidPathException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.nio.file.Path;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.FileVisitResult;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.stream.Stream;
import java.io.BufferedWriter;
import java.io.InputStream;

public class RecursiveWalk extends Walk {
	public RecursiveWalk(BufferedWriter out, String fileName) {
		super(out, fileName);
	}
	public RecursiveWalk(BufferedWriter out) {
		this(out, null);
	}

	private class Visitor extends SimpleFileVisitor<Path> {
		@Override
		public FileVisitResult visitFile(Path file, BasicFileAttributes attr) {
			if (attr.isRegularFile()) {
				processFile(file.toString());
			}
			return FileVisitResult.CONTINUE;
		}
	}

	private void processDir(String path) {
		try {
			Files.walkFileTree(Paths.get(path), this.new Visitor());
		} catch (NoSuchFileException e) {
			printFileAndHash(0, e.getFile());
		} catch (IOException e) {
			printError(path, "directory listing error", e);
		}
	}

	private void processFile(String path) {
		super.process(path);
	}

	@Override
	protected void process(String path) {
		try {
			if (Files.isDirectory(Paths.get(path))) {
				processDir(path);
			} else {
				processFile(path);
			}
		} catch (InvalidPathException e) {
			printFileAndHash(0, path);
		}
	}

	public static void main(String[] args) {
		if (!checkArgs(args)) {
			System.err.println("wrong arguments");
			return;
		}
		start(args[0], args[1], (x, s) -> new RecursiveWalk(x, s));
	}
}

