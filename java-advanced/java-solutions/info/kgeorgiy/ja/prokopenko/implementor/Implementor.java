/**
 * @author Prokopenko Kirill M3236
 */
package info.kgeorgiy.ja.prokopenko.implementor;

import info.kgeorgiy.java.advanced.implementor.*;

import java.nio.file.Path;
import java.nio.file.Files;
import java.util.List;
import java.nio.file.Paths;
import java.io.IOException;
import java.io.InputStream;
import java.io.FileOutputStream;
import java.nio.file.Files;
import java.io.File;
import java.io.Writer;
import java.io.BufferedWriter;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.Constructor;
import java.util.function.BiFunction;
import java.util.ArrayList;
import java.util.Set;
import java.util.zip.ZipEntry;
import java.util.HashSet;
import java.util.jar.JarOutputStream;
import java.net.URISyntaxException;

import javax.tools.JavaCompiler;
import javax.tools.ToolProvider;

/**
 * "Default value" implementation of {@link Impler} interface.
 *
 * @see #implement(Class, Path)
 * @see #implementJar(Class, Path)
 */
public class Implementor implements JarImpler {
	/** Writer wrapper to encode non-ascii chars. */
	private static class EncodingAppendable implements Appendable {
		/** chained appendable */
		private final Appendable up;

		/**
		 * @param up chained appendable
		 */
		public EncodingAppendable(Appendable up) {
			this.up = up;
		}

		/**
		 * Encodes character.
		 *
		 * If character is ascii write as it is, otherwise as {@code u%04x}
		 *
		 * @param c character to encode
		 *
		 * @return {@code this}
		 */
		@Override
		public EncodingAppendable append(char c) throws IOException {
			if (c < 128) {
				up.append(c);
			} else {
				up.append(String.format("\\u%04x", (int)c));
			}
			return this;
		}
		/**
		 * Appends sequence char by char.
		 *
		 * {@inheritDoc}
		 */
		@Override
		public EncodingAppendable append(final CharSequence csq) throws IOException {
			return append(csq, 0, csq.length());
		}
		/**
		 * Appends sequence char by char.
		 *
		 * Appends {@code csq} as [start; end)
		 *
		 * {@inheritDoc}
		 */
		@Override
		public EncodingAppendable append(final CharSequence csq, int start, final int end) throws IOException {
			for (; start < end; start++) {
				append(csq.charAt(start));
			}
			return this;
		}
	}

	/**
	 * Get string literal with default value for type.
	 * @param type type token
	 * @return "null" for object; "false" for boolean; "" for {@code void}; "0" for other primitive types
	 */
	private String getReturn(final Class<?> type) {
		if (!type.isPrimitive()) {
			return "null";
		}
		if (type.equals(boolean.class)) {
			return "false";
		}
		if (type.equals(void.class)) {
			return "";
		}
		return "0";
	}
	/**
	 * Format argument name.
	 *
	 * Argument is named as "final a%d", where d is {@code count}. Comma is added before if needed.
	 *
	 * @param count index of argument
	 * @param type parameter type token
	 * @return formated argument name
	 */
	private String getArgumentName(final int count, final Class<?> type) {
		return String.format("%sfinal %s a%d", count == 0 ? "" : ",", type.getCanonicalName(), count);
	}
	/**
	 * Get string describing {@code throws} declaration.
	 * @param count index of {@code type} in {@code throws} declaration
	 * @param type class describing exception type of checked exception.
	 *
	 * @return exception name prefixed with either {@code throws} or comma
	 */
	private String getThrows(final int count, final Class<?> type) {
		return String.format("%s%s", count == 0 ? "throws " : ",", type.getCanonicalName());
	}
	/**
	 * Wrapper to implement list headers.
	 *
	 * E.g. function arguments, throws
	 *
	 * @param appendable output
	 * @param func mapper from index and type to string to be written
	 * @param types array of types (e.g. acquired from {@link Method#getParameterTypes()})
	 *
	 * @throws IOException (propogates from appendable)
	 */
	private void implementHeader(final Appendable appendable,
	                             final BiFunction<Integer, Class<?>, String> func,
	                             final Class<?>[] types) throws IOException {
		int cnt = 0;
		for (final Class<?> clazz: types) {
			appendable.append(func.apply(cnt, clazz));
			cnt++;
		}
	}
	/**
	 * Removes rudiment modifiers before method implementation.
	 *
	 * @param modifiers declared modifiers
	 * @return filtered {@code modifiers}
	 *
	 * @see Modifier
	 */
	private static int filterMethodModifiers(int modifiers) {
		modifiers &= ~Modifier.ABSTRACT;
		modifiers &= ~Modifier.TRANSIENT;
		modifiers &= ~Modifier.NATIVE;
		modifiers &= ~Modifier.VOLATILE;
		return modifiers;
	}

	/**
	 * Check that method may be overridden
	 *
	 * @param modifiers method modifiers
	 * @return true if and only if method <b>can't</b> be overridden.
	 */
	private boolean isBadMethodModifiers(final int modifiers) {
		return Modifier.isFinal(modifiers)
			|| Modifier.isPrivate(modifiers)
			|| Modifier.isStatic(modifiers)
			|| !Modifier.isAbstract(modifiers)
			;
	}

	/**
	 * Implements provided method.
	 *
	 * @param appendable output
	 * @param method method to implement
	 *
	 * @throws IOException (propogates from {@code appendable})
	 */
	private void implement(final Appendable appendable, final Method method) throws IOException {
		var retType = method.getReturnType();
		int modifiers = method.getModifiers();
		if (isBadMethodModifiers(modifiers)) {
			return;
		}
		modifiers = filterMethodModifiers(modifiers);

		appendable.append(String.format("@Override %s %s %s(", Modifier.toString(modifiers), retType.getCanonicalName(), method.getName()));
		implementHeader(appendable, this::getArgumentName, method.getParameterTypes());
		appendable.append(")");

		// our methods do not throw and may narrow throws => no declaration
		// implementHeader(appendable, this::getThrows, method.getExceptionTypes());

		appendable.append(String.format("{return %s;}", getReturn(retType)));
	}

	/**
	 * Appends absent methods from {@code methods} to {@code list}.
	 *
	 * @param methods methods to add
	 * @param list resulting list of unique methods
	 * @param declared internal argument for storing unique names
	 */
	private void appendMethods(Method[] methods, List<Method> list, Set<String> declared) {
		for (Method method : methods) {
			StringBuilder builder = new StringBuilder();
			builder.append(method.getName());
			builder.append(" ");
			for (Class<?> arg : method.getParameterTypes()) {
				builder.append(arg.getCanonicalName());
				builder.append(" ");
			}
			String asStr = builder.toString();
			if (declared.contains(asStr)) {
				continue;
			}
			declared.add(asStr);
			if (isBadMethodModifiers(method.getModifiers())) {
				continue;
			}
			list.add(method);
		}
	}

	/**
	 * Finds all declared <b>abstract</b> that can be overriden metods in {@code token}.
	 *
	 * Puts them into {@code list}
	 *
	 * Silentrly ignores {@link SecurityException} in {@link Class#getDeclaredMethods}
	 *
	 * @param token class token to scrap methods from, if it is {@code null} returns
	 * @param list resulting list
	 * @param declared set of all declared methods
	 */
	private void scrapMethods(Class<?> token, List<Method> list, Set<String> declared) {
		if (token == null) {
			return;
		}
		try {
			appendMethods(token.getDeclaredMethods(), list, declared);
		} catch (final SecurityException ignored) {
		}
		appendMethods(token.getMethods(), list, declared);
		scrapMethods(token.getSuperclass(), list, declared);
		for (Class<?> clazz : token.getInterfaces()) {
			scrapMethods(clazz, list, declared);
		}
	}
	/**
	 * Finds all declared <b>abstract</b> that can be overridden methods in {@code token}.
	 *
	 * @param token token to search in
	 *
	 * @return list of found methods.
	 */
	private List<Method> scrapMethods(Class<?> token) {
		List<Method> lst = new ArrayList<>();
		Set<String> was = new HashSet<>();
		scrapMethods(token, lst, was);
		return lst;
	}
	/**
	 * Implements all <b>abstract</b> methods which can be overriden.
	 *
	 * @param appendable output
	 * @param token class token to implement
	 *
	 * @throws IOException propogated from {@code appendable}
	 * @throws ImplerException if class can't be implemented: it is final, primitive, has no suitable constructors
	 */
	private void implement(final Appendable appendable, final Class<?> token) throws IOException, ImplerException {
		Package packge = token.getPackage();
		if (packge != null) {
			appendable.append(String.format("package %s;", packge.getName()));
		}
		appendable.append(String.format("public class %sImpl %s %s{", token.getSimpleName(), token.isInterface() ? "implements" : "extends", token.getCanonicalName()));
		for (Method m : scrapMethods(token)) {
			implement(appendable, m);
		}
		boolean goodConstructors = token.getDeclaredConstructors().length == 0;
		for (Constructor<?> i : token.getDeclaredConstructors()) {
			goodConstructors |= implement(appendable, token, i);
		}
		if (!goodConstructors) {
			throw new ImplerException("no constructors");
		}
		appendable.append("}");
	}
	/**
	 * Implements constructor.
	 *
	 * @param appendable output
	 * @param token class that we are implementing
	 * @param ctor constructor
	 *
	 * Forwards arguments (unchecked)
	 * @throws IOException propogated from {@code appendable}
	 *
	 * @return {@code true} if and only if {@code ctor} was implemented
	 */
	private boolean implement(final Appendable appendable, final Class<?> token, final Constructor<?> ctor) throws IOException {
		int modifiers = ctor.getModifiers();
		if (Modifier.isPrivate(modifiers)) {
			return false;
		}
		modifiers = filterMethodModifiers(modifiers);
		appendable.append(String.format("%s %sImpl(", Modifier.toString(modifiers), token.getSimpleName()));
		// here is a problem: generic parameters
		// which generates "note: unchecked"
		// but without bonus
		// we may ignore generics
		implementHeader(appendable, this::getArgumentName, ctor.getParameterTypes());
		appendable.append(")");
		implementHeader(appendable, this::getThrows, ctor.getExceptionTypes());
		appendable.append("{super(");
		implementHeader(appendable,
			(Integer i, Class<?> a) -> String.format("%sa%d", i == 0 ? "" : ",", i),
			ctor.getParameterTypes());
		appendable.append(");}");
		return true;
	}

	/**
	 * get path to implementation file.
	 *
	 * @param token class token of class to implement.
	 * @param root base directory
	 * @param suffix file suffix -- "Impl.java" for example
	 * @return path to '.java' within {@code root}
	 * @throws ImplerException if directory can't be created
	 */
	private Path getImplementationFile(final Class<?> token, final Path root, final String suffix) throws ImplerException {
		Package packge = token.getPackage();
		String[] splitted = packge != null ? packge.getName().split("\\.") : new String[0];
		Path resolved = root.resolve(Paths.get("", splitted));
		if (splitted.length != 0) {
			try {
				Files.createDirectories(resolved);
			} catch (final Exception e) {
				throw new ImplerException("can't create directory " + resolved.toString(), e);
			}
		}
		return resolved.resolve(token.getSimpleName() + suffix);
	}

	/**
	 * {@inheritDoc}
	 *
	 * @throws ImplerException in case of {@link IOException} during writing to the file or in case of {@link SecurityException}
	 */
	@Override
	public void implement(final Class<?> token, final Path root) throws ImplerException {
		if (token.equals(java.lang.Enum.class)) {
			throw new ImplerException("can't implement enum...");
		}
		if (token.isPrimitive()) {
			throw new ImplerException("can't implement primitive type");
		}
		if (token.isArray()) {
			throw new ImplerException("can't implement array");
		}
		final int modifiers = token.getModifiers();
		if (Modifier.isPrivate(modifiers)) {
			throw new ImplerException("can't implement private");
		}
		if (Modifier.isFinal(modifiers)) {
			throw new ImplerException("can't implement final");
		}
		
		try (Writer writer = Files.newBufferedWriter(getImplementationFile(token, root, "Impl.java"))) {
			Appendable encoder = new EncodingAppendable(writer);
			implement(encoder, token);
			/* debug
			var v2 = new BufferedWriter(new OutputStreamWriter(System.out));
			System.out.println("\t>>>>>" + resolved.toString());
			implement(v2, token);
			v2.flush();
			//*/
		} catch (final SecurityException e) {
			throw new ImplerException("security error occured", e);
		} catch (final IOException e) {
			throw new ImplerException("write error occured", e);
		}
	}

	/**
	 * {@inheritDoc}
	 *
	 * @throws ImplerException in case of {@link IOException} during writing to file or in case of {@link SecurityException}
	 */
	public void implementJar(final Class<?> token, final Path jarPath) throws ImplerException {
		final JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
		if (compiler == null) {
			throw new ImplerException("no system default compiler");
		}
		final String tempDir = "." + File.separator + "temp";
		final Path root = Paths.get(tempDir, "compiler");

		implement(token, root);

		final String classPath;
		try {
			classPath = Path.of(Impler.class.getProtectionDomain().getCodeSource().getLocation().toURI()).toString();
		} catch (final URISyntaxException e) {
			throw new ImplerException(e);
		}
		final String[] args = new String[] {
			"-cp", classPath,
			"-d", root.toString(),
			getImplementationFile(token, root, "Impl.java").toString()
		};
		final int exitCode = compiler.run(null, null, null, args);
		if (exitCode != 0) {
			throw new ImplerException("compilation failed");
		}
		final Path baseGeneratedPath = getImplementationFile(token, Paths.get(""), "Impl.class");
		final String baseGeneratedPathSlashed = baseGeneratedPath.toString().replace(File.separator, "/");
		final Path generatedClassPath = root.resolve(baseGeneratedPath);
		try (JarOutputStream jar = new JarOutputStream(Files.newOutputStream(jarPath))) {
			jar.putNextEntry(new ZipEntry(baseGeneratedPathSlashed));
			try (InputStream input = Files.newInputStream(generatedClassPath)) {
				input.transferTo(jar);
			}
			jar.closeEntry();
		} catch (final IOException e) {
			throw new ImplerException(e);
		}
	}

	/**
	 * Help for system args displaying function.
	 *
	 * Prints to {@link System#err}
	 */
	private static void showHelp() {
		System.err.println("usage :");
		System.err.println("\t1) -jar <class-name> <jar-path>");
		System.err.println("\t2) <class-name> <root-path>");
	}

	/**
	 * startup function
	 *
	 * @param args system arguments
	 *
	 * @throws ImplerException in case of implementation error
	 */
	public static void main(final String[] args) throws ImplerException {
		if (args.length < 1) {
			showHelp();
			return;
		}
		final boolean isJar;
		final int argOffset;
		if (args[0].equals("-jar")) {
			isJar = true;
			argOffset = 1;
		} else {
			isJar = false;
			argOffset = 0;
		}
		if (args.length != argOffset + 2) {
			showHelp();
			return;
		}
		final Class<?> clazz;
		try {
			clazz = Class.forName(args[argOffset + 0]);
		} catch (final ClassNotFoundException e) {
			System.err.format("Class %s not found\n", args[argOffset + 0]);
			return;
		}
		final Path path = Paths.get(args[argOffset + 1]);
		JarImpler self = new Implementor();
		if (isJar) {
			self.implementJar(clazz, path);
		} else {
			self.implement(clazz, path);
		}
	}
}
