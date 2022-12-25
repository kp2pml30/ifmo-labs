select StudentId, StudentName, GroupId
from
	Students
where
	GroupId in (
		select Groups.GroupId
		from Groups
		where
			GroupName = :GroupName
	);
