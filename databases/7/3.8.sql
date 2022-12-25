update Students
set
	Debts = (
		select count(distinct Plan.CourseId)
		from
			Students S
			natural join Plan
			natural left join Marks
		where
			Marks.Mark is null
			and Students.StudentId = S.StudentId
	),
	Marks = (
		select count(*)
		from Marks
		where Marks.StudentId = Students.StudentId
	)
where 1 = 1