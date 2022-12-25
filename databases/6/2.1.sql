select
	Students.StudentId, StudentName, GroupName
from Students, Groups
where
	Groups.GroupId = Students.GroupId;