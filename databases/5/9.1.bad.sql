select
	avg(Mark) as AvgMark
from
	Students
		natural join Plan
		left join Marks
			on Students.StudentId = Marks.StudentId and Plan.CourseId = Marks.CourseId
where
	Students.StudentId = :StudentId;