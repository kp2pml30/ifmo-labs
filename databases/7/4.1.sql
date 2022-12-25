insert into Marks
select
	nm.StudentId, nm.CourseId, nm.Mark
from NewMarks nm left join Marks m using (StudentId, CourseId)
where m.Mark is null