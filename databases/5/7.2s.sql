select
	GroupName, CourseName
from
	(
		select distinct
			CiGi.GroupId, CiGi.CourseId
		from
			(select distinct CourseId, GroupId from Students natural join Marks) CiGi
			natural join Students
			left join
				Marks
				on (Students.StudentId = Marks.StudentId and CiGi.CourseId = Marks.CourseId)
		group by
			CiGi.GroupId, CiGi.CourseId
		having
			count(Marks.Mark) = count(*)
	) SUB
	natural join Groups
	natural join Courses;