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
	)
where
	Students.GroupId in (
		select G.GroupId
		from Groups G
		where G.GroupName = :GroupName
	)