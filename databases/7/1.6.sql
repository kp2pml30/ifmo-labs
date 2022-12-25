delete
from
	Students
where
	Students.StudentId in (
		select S.StudentId
		from
			Students S
			natural join Plan
			left join Marks
				on (Plan.CourseId = Marks.CourseId
					and Marks.StudentId = S.StudentId)
		group by S.StudentId
		having count(Marks.Mark) < count(*)
	)