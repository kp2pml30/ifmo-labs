delete
from
	Students
where
	StudentId not in (
		select Marks.StudentId
		from Marks
		group by Marks.StudentId
		having count(*) > 3
	)