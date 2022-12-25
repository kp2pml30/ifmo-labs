delete
from
	Students
where
	StudentId in (
		select Marks.StudentId
		from Marks
		group by Marks.StudentId
		having count(*) >= 3
	)