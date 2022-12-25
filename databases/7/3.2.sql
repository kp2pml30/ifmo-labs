update
	Students
set
	Marks = (
		select count(*) as Marks
		from Marks
		where Marks.StudentId = Students.StudentId
	)
where 1 = 1