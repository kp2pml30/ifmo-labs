select StudentId
from Students
where
	Students.GroupId not in (
		select Plan.GroupId
		from Plan
		where
			Plan.LecturerId in (
				select LecturerId
				from Lecturers
				where LecturerName = :LecturerName
			)
			and Plan.CourseId not in (
				select CourseId
				from Marks
				where Marks.StudentId = Students.StudentId
			)
	)