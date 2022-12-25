select
	Students.StudentId
from
	Students
	inner join
		(select distinct CourseId, GroupId from Plan natural join Lecturers where LecturerName = :LecturerName) Cids
		on (Students.GroupId = Cids.GroupId)
	left join Marks on Students.StudentId = Marks.StudentId and Cids.CourseId = Marks.CourseId
group by Students.StudentId
having
	count(Marks.Mark) = count(*);