select
	Students.StudentId, StudentName, GroupName
from Students, Groups
where
	Groups.GroupId = Students.GroupId
	and StudentId not in (
		select Marks.StudentId
		from Marks
		where
			Marks.CourseId in (
				select Courses.CourseId
				from Courses
				where Courses.CourseName = :CourseName
			)
	);