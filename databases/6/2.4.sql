select
	Students.StudentId, StudentName, GroupName
from Students, Groups
where
	Groups.GroupId = Students.GroupId
	and Students.GroupId in (
		select Plan.GroupId
		from Plan
		where
			Plan.CourseId = :CourseId
	)
	and StudentId not in (
		select Marks.StudentId
		from Marks
		where
			Marks.CourseId = :CourseId
	);
