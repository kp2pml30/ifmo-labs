create view StudentDebts as
select
	StudentId,
	(
		select count(distinct CourseId)
		from Students s natural join Plan
		where
			s.StudentId = os.StudentId
			and not exists (
				select *
				from Marks
				where
					Marks.StudentId = s.StudentId
					and Marks.CourseId = Plan.CourseId
			)
	) as Debts
from Students os