update Students
set
	GroupId = (
		select GroupId
		from Groups
		where GroupName = :GroupName
	)
where
	GroupId in (select Groups.GroupId from Groups where GroupName = :FromGroupName)