delete
from
	Students
where
	StudentId not in (
		select Marks.StudentId
		from Marks
	)