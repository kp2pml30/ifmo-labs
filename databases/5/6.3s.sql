select distinct StudentId from Marks
except select
	Sids.StudentId
from
	(select distinct StudentId from Marks) Sids
	cross join (select distinct CourseId from Plan natural join Lecturers where LecturerName = :LecturerName) Cids
	left join Marks on Sids.StudentId = Marks.StudentId and Cids.CourseId = Marks.CourseId
where
	Marks.Mark is null;