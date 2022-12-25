create view Debts as
select StudentId, count(CourseId) as Debts
from (
	select distinct StudentId, CourseId
	from Students natural join Plan
	except select StudentId, CourseId
	from Marks
) sub
group by StudentId