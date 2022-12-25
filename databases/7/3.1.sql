update
	Students
set
	Marks = (
		select count(*) as Marks
		from Marks
		where Marks.StudentId = :StudentId
	)
where
	StudentId = :StudentId
