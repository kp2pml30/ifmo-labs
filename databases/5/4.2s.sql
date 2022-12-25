select
	StudentId, StudentName, GroupId
from
	Students
		inner join Plan using (GroupId)
		inner join Courses using (CourseId)
where
	CourseName = :CourseName
except select
	StudentId, StudentName, GroupId
from
	Students
		inner join Marks using (StudentId)
		inner join Courses using (CourseId)
where
	CourseName = :CourseName;