select GroupName, CourseName
from Groups, Courses
where
	not exists (
		select *
		from Students
		where
			Students.GroupId = Groups.GroupId
			and not exists (
				select *
				from Marks
				where
					Marks.StudentId = Students.StudentId
					and Marks.CourseId = Courses.CourseId
			)
	);