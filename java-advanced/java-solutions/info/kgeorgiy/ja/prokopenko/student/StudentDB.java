package info.kgeorgiy.ja.prokopenko.student;

import info.kgeorgiy.java.advanced.student.*;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.function.BinaryOperator;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.stream.Collector;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class StudentDB implements GroupQuery {
	static private final Comparator<Student> nameComparator = Comparator.comparing(Student::getLastName)
					.thenComparing(Student::getFirstName)
					.reversed()
					.thenComparing(Student::getId);

	private <T, R> R getProperty(final List<Student> students, final Function<Student, T> func, final Collector<? super T, ?, R> collector) {
		return students.stream().map(func).collect(collector);
	}

	private <T> List<T> getProperty(final List<Student> students, final Function<Student, T> func) {
		return getProperty(students, func, Collectors.toList());
	}

	@Override
	public List<String> getFirstNames(final List<Student> students) {
		return getProperty(students, Student::getFirstName);
	}

	@Override
	public List<String> getLastNames(final List<Student> students) {
		return getProperty(students, Student::getLastName);
	}

	@Override
	public List<GroupName> getGroups(final List<Student> students) {
		return getProperty(students, Student::getGroup);
	}

	@Override
	public List<String> getFullNames(final List<Student> students) {
		return getProperty(students, (Student s) -> s.getFirstName() + " " + s.getLastName());
	}

	@Override
	public Set<String> getDistinctFirstNames(final List<Student> students) {
		return getProperty(students, Student::getFirstName, Collectors.toCollection(TreeSet::new));
	}

	private static <T, R> Function<T, Optional<R>> flatMapAlways(Function<T, R> func) {
		return func.andThen(Optional::of);
	}

	@Override
	public String getMaxStudentFirstName(final List<Student> students) {
		return students.stream().max(Comparator.comparing(Student::getId))
			.flatMap(flatMapAlways(Student::getFirstName))
			.orElse("");
	}

	private <T extends Comparable<? super T>> List<Student> getSorted(final Collection<Student> students, final Comparator<? super Student> comp) {
		return students.stream()
			.sorted(comp)
			.collect(Collectors.toList());
	}

	@Override
	public List<Student> sortStudentsById(final Collection<Student> students) {
		return getSorted(students, Comparator.comparing(Student::getId));
	}

	@Override
	public List<Student> sortStudentsByName(final Collection<Student> students) {
		return getSorted(students, nameComparator);
	}

	private <R> R findBy(final Collection<Student> students, final Predicate<? super Student> func, final Collector<? super Student, ?, R> collector) {
		return students.stream()
			.filter(func)
			.sorted(nameComparator)
			.collect(collector);
	}

	private List<Student> findBy(final Collection<Student> students, final Predicate<? super Student> func) {
		return findBy(students, func, Collectors.toList());
	}

	@Override
	public List<Student> findStudentsByFirstName(final Collection<Student> students, final String name) {
		return findBy(students, (Student s) -> name.equals(s.getFirstName()));
	}

	@Override
	public List<Student> findStudentsByLastName(final Collection<Student> students, String name) {
		return findBy(students, (Student s) -> name.equals(s.getLastName()));
	}

	@Override
	public List<Student> findStudentsByGroup(final Collection<Student> students, final GroupName group) {
		return findBy(students, (Student s) -> group.equals(s.getGroup()));
	}

	@Override
	public Map<String, String> findStudentNamesByGroup(final Collection<Student> students, GroupName group) {
		return findBy(students,
			(Student s) -> Objects.equals(s.getGroup(), group),
			Collectors.toMap(Student::getLastName, Student::getFirstName,
				BinaryOperator.minBy(Comparator.naturalOrder())));
	}

	private List<Group> getGroupsBy(final Collection<Student> students, final Comparator<? super Student> comparator) {
		return students.stream().collect(Collectors.groupingBy(Student::getGroup))
			.entrySet().stream()
			.map((Map.Entry<GroupName, List<Student>> e) -> new Group(e.getKey(),
				e.getValue().stream()
					.sorted(comparator).collect(Collectors.toList())))
			.sorted(Comparator.comparing(Group::getName))
			.collect(Collectors.toList());
	}

	@Override
	public List<Group> getGroupsByName(final Collection<Student> students) {
		return getGroupsBy(students, nameComparator);
	}

	@Override
	public List<Group> getGroupsById(final Collection<Student> students) {
		return getGroupsBy(students, Comparator.comparing(Student::getId));
	}

	private static <T, R> Function<T, R> functionCast(Function<T, R> func) {
		return func;
	}

	private <R> GroupName getLargestGroupBy(final Collection<Student> students,
	                                    final Collector<? super Student, ?, R> collector,
	                                    final Function<R, Integer> sizeGetter,
	                                    final Comparator<? super GroupName> nameComparator) {
		return students.stream()
			.collect(Collectors.groupingBy(Student::getGroup, collector))
			.entrySet().stream()
			.max(Comparator.comparing(functionCast(Map.Entry<GroupName, R>::getValue).andThen(sizeGetter))
				.thenComparing(Map.Entry::getKey, nameComparator))
			.flatMap(flatMapAlways(Map.Entry::getKey))
			.orElse(null);
	}

	@Override
	public GroupName getLargestGroup(final Collection<Student> students) {
		return getLargestGroupBy(students,
				Collectors.toList(),
				Collection::size,
				Comparator.naturalOrder());
	}

	@Override
	public GroupName getLargestGroupFirstName(final Collection<Student> students) {
		return getLargestGroupBy(students,
				Collectors.toMap(Student::getFirstName, Function.identity(), (a, b) -> a),
				Map::size,
				Comparator.reverseOrder());
	}
}
