create view StudentMarks as
select StudentId, count(m.Mark) as Marks
from Students natural left join Marks  m
group by StudentId