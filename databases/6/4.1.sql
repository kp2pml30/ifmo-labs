select
	StudentName, CourseName
from
	Students, Courses
where
	exists (
		select *
		from Plan
		where
			Plan.GroupId = Students.GroupId
			and Plan.CourseId = Courses.CourseId
	)
	and not exists (
		select *
		from Marks
		where
			Marks.StudentId = Students.StudentId
			and Marks.CourseId = Courses.CourseId
	);