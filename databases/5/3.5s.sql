select
	Students.StudentId, StudentName, Students.GroupId
from
	Marks
		natural join Plan
		inner join Students using (StudentId)
where
	Mark = :Mark and LecturerId = :LecturerId;