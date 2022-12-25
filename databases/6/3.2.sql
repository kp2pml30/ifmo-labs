select
	StudentName, CourseName
from
	Students as S, Courses as C
where
	exists (
		select
			StudentId, CourseId
		from
			Students, Plan
		where
			Plan.GroupId = Students.GroupId
			and S.StudentId = StudentId
			and C.CourseId = CourseId
		union select
			StudentId, CourseId
		from
			Marks
		where
			S.StudentId = StudentId
			and C.CourseId = CourseId
	);