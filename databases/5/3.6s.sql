select
	Students.StudentId, StudentName, Students.GroupId
from
	Marks
		natural join Plan
		natural join Lecturers
		inner join Students using (StudentId)
where
	Mark = :Mark and LecturerName = :LecturerName;