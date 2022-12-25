select StudentId
from Students
where
	not exists (
		select *
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