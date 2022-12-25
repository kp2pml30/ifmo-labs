select distinct
	Students.StudentId
from
	Students
		left join
			(Lecturers natural join Plan)
			on Students.GroupId = Plan.GroupId
		inner join
			Marks
			on Marks.StudentId = Students.StudentId
				and Marks.CourseId = Plan.CourseId
where
	LecturerName = :LecturerName;