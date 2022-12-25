create view AllMarks as
select StudentId, count(mnm.Mark) as Marks
from
	Students
	natural left join (
		select StudentId, Mark
		from Marks
		union all
		select StudentId, Mark
		from NewMarks
	) mnm
group by StudentId