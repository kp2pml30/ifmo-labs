select StudentId, StudentName, GroupId
from
	Students
where
	StudentId in (
		select Marks.StudentId
		from Marks
		where
			Marks.Mark = :Mark
			and Marks.CourseId in (
				select Courses.CourseId
				from Courses
				where
					CourseName = :CourseName
			)
	);