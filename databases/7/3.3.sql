update
	Students
set
	Marks = Marks + (
		select count(*) as Marks
		from NewMarks
		where NewMarks.StudentId = Students.StudentId
	)
where 1 = 1